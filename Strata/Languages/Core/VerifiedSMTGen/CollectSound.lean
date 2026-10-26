/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.ProofObligation
import all Strata.Languages.Core.VerifiedSMTGen.ProofObligation
public import Strata.Languages.Core.VerifiedSMTGen.SharedWF
import all Strata.Languages.Core.VerifiedSMTGen.SharedWF
public import Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.Util.ListMap

/-!
# Refactored SMT encoder — collect soundness (ProofObligation ⟶ CoreCtx)

Statement C: `collect_WF` (`ProofObligation.WF ⟹ CoreCtx.WF ∧ CoreCtx.NamesWF`) and `collect_valid`
(`CoreCtx.Valid ⟹ ProofObligation.Valid`). The end-to-end composition with the translate phase lives in
`EncoderSound`.
-/

open Core Lambda Imperative Strata.SMT Std

namespace Core.Refactor

/-! ## Collect-phase structural correspondence
The function/type closures leave the program chunks (`assumptions`/`distincts`/`varDefs`) alone, and
every collected `fnDef`/`fnAxiom` is materialized from some `f ∈ F.toArray`.
-/

/-- The raw partition context — the program-level chunks an obligation reduces to before the
    function/type closures run. Abbreviation for `CoreCtx.addObligationEntries {} d`. -/
abbrev obligationBaseCtx (d : Imperative.ProofObligation Expression) : CoreCtx :=
  CoreCtx.addObligationEntries {} d

/-- The `collectFuncs`-fold state (reachable names marked in `seenFns`; `ctx` still the raw partition). -/
abbrev collectFuncsState (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (d : Imperative.ProofObligation Expression) :
    CollectState :=
  (obligationExprs d).foldl (collectFuncs uAT F tf)
    { ctx := { (obligationBaseCtx d) with
        varDecls := unmanagedFVars d ++ (obligationBaseCtx d).varDecls } }

/-- A `List.foldl` of a `CollectState`-step preserving a `CoreCtx` projection preserves it overall. -/
theorem foldl_ctx_proj {α β : Type} {g : CollectState → α → CollectState} (proj : CoreCtx → β)
    (hg : ∀ (st : CollectState) (a : α), proj (g st a).ctx = proj st.ctx) :
    ∀ (l : List α) (st : CollectState), proj (l.foldl g st).ctx = proj st.ctx := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a t ih => intro st; rw [List.foldl_cons, ih (g st a), hg st a]

/-- The function-reachability worklist never touches the resolved `CoreCtx` (it only threads
    `seenFns`). -/
theorem collectFuncsGo_ctx (uAT : Bool) (F : Lambda.Factory CoreLParams) (dtOps : List String) :
    ∀ (st : CollectState) (wl : List String),
      (collectFuncsGo uAT F dtOps st wl).ctx = st.ctx := by
  intro st wl
  fun_induction collectFuncsGo uAT F dtOps st wl <;>
    simp_all [CollectState.markFuncSeen]

/-- `addDatatype` / `addSort` only change `datatypes`/`datatypeFuns`/`sorts` (and `seenTypes`), so any
    projection landing outside those is preserved. Both are `rfl` per field. -/
theorem collectTypesGo_ctx_proj (uAT : Bool) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (karities : KnownTypeArities) {β : Type} (proj : CoreCtx → β)
    (hdt : ∀ (st : CollectState) d, proj (st.addDatatype d).ctx = proj st.ctx)
    (hsort : ∀ (st : CollectState) n a, proj (st.addSort n a).ctx = proj st.ctx) :
    ∀ (st : CollectState) (wl : List String),
      proj (collectTypesGo uAT tf karities st wl).ctx = proj st.ctx := by
  intro st wl
  fun_induction collectTypesGo uAT tf karities st wl <;>
    simp_all

/-- One materialization step (`addFunc`) leaves `assumptions`/`distincts`/`varDefs` unchanged — it only
    appends to `fnAxioms` and one of `fnDefs`/`fnDecls`. -/
theorem addFunc_chunks (st : CollectState) (f : LFunc CoreLParams) :
    (st.addFunc f).ctx.assumptions = st.ctx.assumptions ∧
    (st.addFunc f).ctx.distincts = st.ctx.distincts ∧
    (st.addFunc f).ctx.varDefs = st.ctx.varDefs := by
  unfold CollectState.addFunc
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- `addFunc` never changes `seenFns` (it only appends to the `ctx` chunks). -/
theorem addFunc_seenFns (st : CollectState) (f : LFunc CoreLParams) :
    (st.addFunc f).seenFns = st.seenFns := by
  unfold CollectState.addFunc; split <;> rfl

/-- The materialize step preserves `seenFns`. -/
theorem matStep_seenFns (st : CollectState) (f : LFunc CoreLParams) :
    (if st.seenFns.contains f.name.name then st.addFunc f else st).seenFns = st.seenFns := by
  split
  · exact addFunc_seenFns st f
  · rfl

/-- `materializeFuncs` (an `Array.foldl` of `addFunc`) preserves any projection that `addFunc` preserves. -/
theorem materializeFuncs_ctx_proj (st : CollectState) (F : Lambda.Factory CoreLParams)
    {β : Type} (proj : CoreCtx → β)
    (hstep : ∀ (s : CollectState) (f : LFunc CoreLParams), proj (s.addFunc f).ctx = proj s.ctx) :
    proj (st.materializeFuncs F).ctx = proj st.ctx := by
  unfold CollectState.materializeFuncs
  rw [← Array.foldl_toList]
  refine foldl_ctx_proj proj ?_ F.toArray.toList st
  intro s f
  by_cases h : s.seenFns.contains f.name.name = true
  · simp only [h, if_true]; exact hstep s f
  · simp only [h, if_false, Bool.false_eq_true]

/-- The function-reachability walk on a single expression never touches the resolved `CoreCtx`. -/
theorem collectFuncs_ctx (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (s : CollectState) (e : Expression.Expr) :
    (collectFuncs uAT F tf s e).ctx = s.ctx := by
  unfold collectFuncs; exact collectFuncsGo_ctx uAT F _ s _

/-! ## `seenTypes` invariance under the function walk (only the type walk `addDatatype`/`addSort`
touches `seenTypes`) — needed to show the block-regrouped `datatypes` is empty on the base fragment.
-/

/-- `addFunc` only rewrites `ctx`, so `seenTypes` is untouched. -/
theorem addFunc_seenTypes (st : CollectState) (f : LFunc CoreLParams) :
    (st.addFunc f).seenTypes = st.seenTypes := by
  unfold CollectState.addFunc; rfl

/-- `materializeFuncs` (an `Array.foldl` of `addFunc`) preserves `seenTypes`. -/
theorem materializeFuncs_seenTypes (st : CollectState) (F : Lambda.Factory CoreLParams) :
    (st.materializeFuncs F).seenTypes = st.seenTypes := by
  unfold CollectState.materializeFuncs
  rw [← Array.foldl_toList]
  induction F.toArray.toList generalizing st with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · exact addFunc_seenTypes st f
    · rfl

/-- The function-reachability walk records only `seenFns`, never `seenTypes`. -/
theorem collectFuncsGo_seenTypes (uAT : Bool) (F : Lambda.Factory CoreLParams) (dtOps : List String) :
    ∀ (st : CollectState) (wl : List String),
      (collectFuncsGo uAT F dtOps st wl).seenTypes = st.seenTypes := by
  intro st wl
  fun_induction collectFuncsGo uAT F dtOps st wl <;>
    simp_all [CollectState.markFuncSeen]

theorem collectFuncs_seenTypes (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (s : CollectState) (e : Expression.Expr) :
    (collectFuncs uAT F tf s e).seenTypes = s.seenTypes := by
  unfold collectFuncs; exact collectFuncsGo_seenTypes uAT F _ s _

/-- A `List.foldl` of a `seenTypes`-preserving step preserves `seenTypes`. -/
theorem foldl_seenTypes_fixed {α : Type} {g : CollectState → α → CollectState}
    (hstep : ∀ (s : CollectState) (e : α), (g s e).seenTypes = s.seenTypes) :
    ∀ (l : List α) (s : CollectState), (l.foldl g s).seenTypes = s.seenTypes
  | [], _ => rfl
  | e :: rest, s => by rw [List.foldl_cons, foldl_seenTypes_fixed hstep rest, hstep]

/-- **Projection-generic collect preservation.** Any `CoreCtx` projection that `addDatatype`/`addSort`/
    `addFunc` all preserve, and that is unchanged by the front-seeded `varDecls` update, equals its value
    on the raw partition `obligationBaseCtx d`. -/
theorem collectObligation_proj {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) {β : Type} (proj : CoreCtx → β)
    (hdt : ∀ (st : CollectState) d', proj (st.addDatatype d').ctx = proj st.ctx)
    (hsort : ∀ (st : CollectState) n a, proj (st.addSort n a).ctx = proj st.ctx)
    (hfunc : ∀ (st : CollectState) (f : LFunc CoreLParams), proj (st.addFunc f).ctx = proj st.ctx)
    (hset : ∀ (c : CoreCtx) (bs : List (List (LDatatype CoreLParams.IDMeta))),
        proj { c with datatypes := bs } = proj c)
    (hbase : proj { (obligationBaseCtx d) with
        varDecls := unmanagedFVars d ++ (obligationBaseCtx d).varDecls } = proj (obligationBaseCtx d)) :
    proj (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) = proj (obligationBaseCtx d) := by
  simp only [collectObligation]
  rw [hset]
  rw [foldl_ctx_proj proj
        (fun s e => by unfold collectTypes; exact collectTypesGo_ctx_proj uAT tf karities proj hdt hsort s _)]
  rw [materializeFuncs_ctx_proj _ F proj hfunc]
  rw [foldl_ctx_proj proj (fun s e => by rw [collectFuncs_ctx])]
  exact hbase

/-- **Program-chunk preservation.** The collected obligation's `assumptions`/`distincts`/`varDefs` are
    exactly the raw partition (`obligationBaseCtx d`). -/
theorem collectObligation_chunks {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) :
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).assumptions
      = (obligationBaseCtx d).assumptions ∧
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).distincts
      = (obligationBaseCtx d).distincts ∧
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).varDefs
      = (obligationBaseCtx d).varDefs :=
  ⟨collectObligation_proj d (·.assumptions) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun s f => (addFunc_chunks s f).1) (fun _ _ => rfl) rfl,
   collectObligation_proj d (·.distincts) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun s f => (addFunc_chunks s f).2.1) (fun _ _ => rfl) rfl,
   collectObligation_proj d (·.varDefs) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun s f => (addFunc_chunks s f).2.2) (fun _ _ => rfl) rfl⟩

/-- **`fnDefs` empty in the raw partition** (`addObligationEntries` writes only the four program chunks). -/
theorem obligationBaseCtx_fnDefs_nil (d : Imperative.ProofObligation Expression) :
    (obligationBaseCtx d).fnDefs = [] := by
  have key : ∀ (c : CoreCtx), (CoreCtx.addObligationEntries c d).fnDefs = c.fnDefs := by
    intro c
    unfold CoreCtx.addObligationEntries
    generalize d.assumptions.flatten = es
    induction es generalizing c with
    | nil => rfl
    | cons a t ih =>
        rw [List.foldl_cons, ih]
        split <;> (try split) <;> rfl
  exact key {}

/-- **`fnDecls` empty in the raw partition.** -/
theorem obligationBaseCtx_fnDecls_nil (d : Imperative.ProofObligation Expression) :
    (obligationBaseCtx d).fnDecls = [] := by
  have key : ∀ (c : CoreCtx), (CoreCtx.addObligationEntries c d).fnDecls = c.fnDecls := by
    intro c
    unfold CoreCtx.addObligationEntries
    generalize d.assumptions.flatten = es
    induction es generalizing c with
    | nil => rfl
    | cons a t ih =>
        rw [List.foldl_cons, ih]
        split <;> (try split) <;> rfl
  exact key {}

/-- **`datatypes` empty in the raw partition.** -/
theorem obligationBaseCtx_datatypes_nil (d : Imperative.ProofObligation Expression) :
    (obligationBaseCtx d).datatypes = [] := by
  have key : ∀ (c : CoreCtx), (CoreCtx.addObligationEntries c d).datatypes = c.datatypes := by
    intro c
    unfold CoreCtx.addObligationEntries
    generalize d.assumptions.flatten = es
    induction es generalizing c with
    | nil => rfl
    | cons a t ih => rw [List.foldl_cons, ih]; split <;> (try split) <;> rfl
  exact key {}

/-- **`datatypeFuns` empty in the raw partition.** -/
theorem obligationBaseCtx_datatypeFuns_empty (d : Imperative.ProofObligation Expression) :
    (obligationBaseCtx d).datatypeFuns = ∅ := by
  have key : ∀ (c : CoreCtx), (CoreCtx.addObligationEntries c d).datatypeFuns = c.datatypeFuns := by
    intro c
    unfold CoreCtx.addObligationEntries
    generalize d.assumptions.flatten = es
    induction es generalizing c with
    | nil => rfl
    | cons a t ih => rw [List.foldl_cons, ih]; split <;> (try split) <;> rfl
  exact key {}

/-- **`fnAxioms` empty in the raw partition.** -/
theorem obligationBaseCtx_fnAxioms_nil (d : Imperative.ProofObligation Expression) :
    (obligationBaseCtx d).fnAxioms = [] := by
  have key : ∀ (c : CoreCtx), (CoreCtx.addObligationEntries c d).fnAxioms = c.fnAxioms := by
    intro c
    unfold CoreCtx.addObligationEntries
    generalize d.assumptions.flatten = es
    induction es generalizing c with
    | nil => rfl
    | cons a t ih =>
        rw [List.foldl_cons, ih]
        split <;> (try split) <;> rfl
  exact key {}

/-! ## INFRASTRUCTURE 2 — every collected `fnDef`/`fnAxiom` is materialized from some `f ∈ F.toArray` -/

/-- `addFunc` always appends the function's axioms to `fnAxioms`. -/
theorem addFunc_fnAxioms_eq (st : CollectState) (f : LFunc CoreLParams) :
    (st.addFunc f).ctx.fnAxioms = st.ctx.fnAxioms ++ f.axioms := by
  unfold CollectState.addFunc; split <;> rfl

/-- Every `fnDef` produced by one `addFunc` is either already present or the materialization of `f`. -/
theorem addFunc_fnDefs_mem (st : CollectState) (f : LFunc CoreLParams) :
    ∀ d' ∈ (st.addFunc f).ctx.fnDefs,
      d' ∈ st.ctx.fnDefs ∨
      (f.isRecursive = false ∧ ∃ body, f.body = some body ∧
        d'.name = f.name.name ∧ d'.argTys = f.inputs.values ∧
        d'.retTy = f.output ∧ d'.body = LExpr.substFvarsLifting body (funcBvarSubst f)) := by
  intro d' hd'
  unfold CollectState.addFunc at hd'
  cases hrec : f.isRecursive
  · cases hbody : f.body
    · simp only [hrec, hbody] at hd'; exact Or.inl hd'
    · rename_i val
      simp only [hrec, hbody] at hd'
      rw [List.mem_append, List.mem_singleton] at hd'
      rcases hd' with h | h
      · exact Or.inl h
      · subst h
        refine Or.inr ⟨rfl, val, rfl, rfl, ?_, rfl, rfl⟩
        show ((f.inputs.keys.map (·.name)).zip f.inputs.values).map (·.2) = f.inputs.values
        apply List.map_snd_zip
        simp [List.length_map, ListMap.keys.length, ListMap.values_eq_map_snd]
  · cases hbody : f.body
    · simp only [hrec, hbody] at hd'; exact Or.inl hd'
    · simp only [hrec, hbody] at hd'; exact Or.inl hd'

/-- Generic list-fold version of the `fnDefs` correspondence (the step is `materializeFuncs`'s lambda). -/
theorem foldl_matStep_fnDefs_mem :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState) (d' : FnDef),
      d' ∈ (l.foldl (fun s f => if s.seenFns.contains f.name.name then s.addFunc f else s) st).ctx.fnDefs →
      d' ∈ st.ctx.fnDefs ∨
      ∃ f ∈ l, f.name.name ∈ st.seenFns ∧ f.isRecursive = false ∧ ∃ body, f.body = some body ∧
        d'.name = f.name.name ∧ d'.argTys = f.inputs.values ∧
        d'.retTy = f.output ∧ d'.body = LExpr.substFvarsLifting body (funcBvarSubst f) := by
  intro l
  induction l with
  | nil => intro st d' h; exact Or.inl h
  | cons a t ih =>
      intro st d' h
      rw [List.foldl_cons] at h
      rcases ih _ d' h with h1 | ⟨f, hf, hfseen, hrec, body, hbody, hname, hargs, hret, hbdy⟩
      · by_cases hc : (st.seenFns.contains a.name.name) = true
        · rw [if_pos hc] at h1
          rcases addFunc_fnDefs_mem st a d' h1 with hh | ⟨hrec, body, hbody, hname, hargs, hret, hbdy⟩
          · exact Or.inl hh
          · have haseen : a.name.name ∈ st.seenFns := by
              simp only [List.contains_eq_mem, decide_eq_true_eq] at hc; exact hc
            exact Or.inr ⟨a, List.mem_cons_self, haseen, hrec, body, hbody, hname, hargs, hret, hbdy⟩
        · rw [if_neg hc] at h1; exact Or.inl h1
      · refine Or.inr ⟨f, List.mem_cons_of_mem _ hf, ?_, hrec, body, hbody, hname, hargs, hret, hbdy⟩
        rwa [matStep_seenFns st a] at hfseen

/-- Generic list-fold version of the `fnAxioms` correspondence. -/
theorem foldl_matStep_fnAxioms_mem :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState) (e : Expression.Expr),
      e ∈ (l.foldl (fun s f => if s.seenFns.contains f.name.name then s.addFunc f else s) st).ctx.fnAxioms →
      e ∈ st.ctx.fnAxioms ∨ ∃ f ∈ l, f.name.name ∈ st.seenFns ∧ e ∈ f.axioms := by
  intro l
  induction l with
  | nil => intro st e h; exact Or.inl h
  | cons a t ih =>
      intro st e h
      rw [List.foldl_cons] at h
      rcases ih _ e h with h1 | ⟨f, hf, hrest⟩
      · by_cases hc : (st.seenFns.contains a.name.name) = true
        · rw [if_pos hc, addFunc_fnAxioms_eq] at h1
          rcases List.mem_append.mp h1 with hh | hh
          · exact Or.inl hh
          · have haseen : a.name.name ∈ st.seenFns := by
              simp only [List.contains_eq_mem, decide_eq_true_eq] at hc; exact hc
            exact Or.inr ⟨a, List.mem_cons_self, haseen, hh⟩
        · rw [if_neg hc] at h1; exact Or.inl h1
      · have hs : f.name.name ∈ st.seenFns := by rw [← matStep_seenFns st a]; exact hrest.1
        exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hs, hrest.2⟩

/-- `materializeFuncs`-level `fnDefs` correspondence. -/
theorem materializeFuncs_fnDefs_mem (st : CollectState) (F : Lambda.Factory CoreLParams) :
    ∀ d' ∈ (st.materializeFuncs F).ctx.fnDefs,
      d' ∈ st.ctx.fnDefs ∨
      ∃ f ∈ F.toArray, f.name.name ∈ st.seenFns ∧ f.isRecursive = false ∧ ∃ body, f.body = some body ∧
        d'.name = f.name.name ∧ d'.argTys = f.inputs.values ∧
        d'.retTy = f.output ∧ d'.body = LExpr.substFvarsLifting body (funcBvarSubst f) := by
  intro d' hd'
  unfold CollectState.materializeFuncs at hd'
  rw [← Array.foldl_toList] at hd'
  rcases foldl_matStep_fnDefs_mem F.toArray.toList st d' hd' with h | ⟨f, hf, hrest⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, by simpa using hf, hrest⟩

/-- `materializeFuncs`-level `fnAxioms` correspondence. -/
theorem materializeFuncs_fnAxioms_mem (st : CollectState) (F : Lambda.Factory CoreLParams) :
    ∀ e ∈ (st.materializeFuncs F).ctx.fnAxioms,
      e ∈ st.ctx.fnAxioms ∨ ∃ f ∈ F.toArray, f.name.name ∈ st.seenFns ∧ e ∈ f.axioms := by
  intro e he
  unfold CollectState.materializeFuncs at he
  rw [← Array.foldl_toList] at he
  rcases foldl_matStep_fnAxioms_mem F.toArray.toList st e he with h | ⟨f, hf, hrest⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, by simpa using hf, hrest⟩

/-- **Reachable-`fnDefs` correspondence for the whole obligation.** Every collected define-fun is
    materialized from some `f ∈ F.toArray` (non-recursive, with a body), with matching name/args/ret/body. -/
theorem collectObligation_fnDefs_mem {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) :
    ∀ d' ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDefs,
      ∃ f ∈ F.toArray, f.name.name ∈ (collectFuncsState uAT F tf d).seenFns ∧
        f.isRecursive = false ∧ ∃ body, f.body = some body ∧
        d'.name = f.name.name ∧ d'.argTys = f.inputs.values ∧
        d'.retTy = f.output ∧ d'.body = LExpr.substFvarsLifting body (funcBvarSubst f) := by
  intro d' hd'
  simp only [collectObligation] at hd'
  rw [foldl_ctx_proj (·.fnDefs)
      (fun s e => by unfold collectTypes
                     exact collectTypesGo_ctx_proj uAT tf karities (·.fnDefs)
                       (fun _ _ => rfl) (fun _ _ _ => rfl) s _)] at hd'
  rcases materializeFuncs_fnDefs_mem _ F d' hd' with h | hcorr
  · exfalso
    rw [foldl_ctx_proj (·.fnDefs) (fun s e => by rw [collectFuncs_ctx])] at h
    have hnil : ((({ ctx := { (CoreCtx.addObligationEntries {} d) with
        varDecls := unmanagedFVars d ++ (CoreCtx.addObligationEntries {} d).varDecls } } : CollectState)).ctx.fnDefs)
        = [] := obligationBaseCtx_fnDefs_nil d
    rw [hnil] at h; exact List.not_mem_nil h
  · exact hcorr

/-- **Reachable-`fnAxioms` correspondence for the whole obligation.** -/
theorem collectObligation_fnAxioms_mem {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) :
    ∀ e ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnAxioms,
      ∃ f ∈ F.toArray, f.name.name ∈ (collectFuncsState uAT F tf d).seenFns ∧ e ∈ f.axioms := by
  intro e he
  simp only [collectObligation] at he
  rw [foldl_ctx_proj (·.fnAxioms)
      (fun s e => by unfold collectTypes
                     exact collectTypesGo_ctx_proj uAT tf karities (·.fnAxioms)
                       (fun _ _ => rfl) (fun _ _ _ => rfl) s _)] at he
  rcases materializeFuncs_fnAxioms_mem _ F e he with h | hcorr
  · exfalso
    rw [foldl_ctx_proj (·.fnAxioms) (fun s e => by rw [collectFuncs_ctx])] at h
    have hnil : ((({ ctx := { (CoreCtx.addObligationEntries {} d) with
        varDecls := unmanagedFVars d ++ (CoreCtx.addObligationEntries {} d).varDecls } } : CollectState)).ctx.fnAxioms)
        = [] := obligationBaseCtx_fnAxioms_nil d
    rw [hnil] at h; exact List.not_mem_nil h
  · exact hcorr

/-! ## Dependent transport helpers for the `DefConsistent`/`Distincts` discharge -/

/-- `applyBVarVal` transported across equal arg/return types and heterogeneously-equal function/valuation. -/
theorem applyBVarVal_heq
    {a₁ a₂ : List LMonoTy} (ha : a₁ = a₂) {r₁ r₂ : LMonoTy} (hr : r₁ = r₂)
    {g₁ : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow r₁ a₁)}
    {g₂ : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow r₂ a₂)}
    (hg : HEq g₁ g₂)
    {bv₁ : Lambda.BVarVal simpTcInterp simpTyVarVal a₁}
    {bv₂ : Lambda.BVarVal simpTcInterp simpTyVarVal a₂} (hbv : HEq bv₁ bv₂) :
    HEq (applyBVarVal a₁ r₁ g₁ bv₁) (applyBVarVal a₂ r₂ g₂ bv₂) := by
  subst ha; subst hr
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hbv
  rfl

/-- `simpDenote` transported across equal binder-context/expression/type and HEq valuation (proofs are
    proof-irrelevant). -/
theorem simpDenote_heq {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp}
    {Δ₁ Δ₂ : BVarCtx} (hΔ : Δ₁ = Δ₂)
    {bv₁ : Lambda.BVarVal simpTcInterp simpTyVarVal Δ₁}
    {bv₂ : Lambda.BVarVal simpTcInterp simpTyVarVal Δ₂} (hbv : HEq bv₁ bv₂)
    {e₁ e₂ : Expression.Expr} (he : e₁ = e₂) {τ₁ τ₂ : LMonoTy} (hτ : τ₁ = τ₂)
    {h₁ : LExpr.HasTypeA Δ₁ e₁ τ₁} {h₂ : LExpr.HasTypeA Δ₂ e₂ τ₂} :
    HEq (simpDenote opInterp fvarVal bv₁ e₁ τ₁ h₁) (simpDenote opInterp fvarVal bv₂ e₂ τ₂ h₂) := by
  subst hΔ; subst he; subst hτ
  obtain rfl := eq_of_heq hbv
  rfl

/-- The `Pairwise (· ≠ ·)` distinctness verdict is invariant under the (unique) choice of base type and
    the (proof-irrelevant) typing witness. -/
theorem pairwise_denote_congr {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp}
    {es : List Expression.Expr} {τ₁ τ₂ : LMonoTy} (hτ : τ₁ = τ₂)
    {h₁ : ∀ x : {y // y ∈ es}, LExpr.HasTypeA [] x.1 τ₁}
    {h₂ : ∀ x : {y // y ∈ es}, LExpr.HasTypeA [] x.1 τ₂}
    (H : (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ₂ (h₂ x))).Pairwise (· ≠ ·)) :
    (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ₁ (h₁ x))).Pairwise (· ≠ ·) := by
  subst hτ
  have hfun : (fun x : {y // y ∈ es} => simpDenote opInterp fvarVal .nil x.1 τ₁ (h₁ x))
            = (fun x => simpDenote opInterp fvarVal .nil x.1 τ₁ (h₂ x)) := by
    funext x; rfl
  rw [hfun]; exact H

/-! ## Reachability-closure support: `.op`-head extraction and typing-side lemmas that connect
`exprFnRefs`/`funcFnRefs` (encoder-defined) with `HasSimpType`/`AppSpine`.
-/

/-- The `(name, arrow-type)` pairs at every annotated `.op`-head of an expression — exactly the pairs
    the `AppSpine.fnOp` rule consults in `Ψ`. -/
def exprFnOps : Expression.Expr → List (String × LMonoTy)
  | .op () o (some oty) => [(o.name, oty)]
  | .app () fn arg => exprFnOps fn ++ exprFnOps arg
  | .ite () c t e => exprFnOps c ++ exprFnOps t ++ exprFnOps e
  | .eq () e1 e2 => exprFnOps e1 ++ exprFnOps e2
  | .quant () _ _ _ tr body => exprFnOps tr ++ exprFnOps body
  | .abs () _ _ e => exprFnOps e
  | _ => []

mutual
/-- **A typed expression's non-predefined function-op pairs are all declared in `Ψ`.** Every
    `p ∈ exprFnOps e` with `isPredefinedOp p.1 = false` has `p ∈ Ψ`. Type-match half of the reachability
    bridge: `HasSimpType`/`AppSpine` consult `Ψ` positively only at `AppSpine.fnOp` — exactly the head
    `exprFnOps` records — so every such collected pair is a witnessed `Ψ` membership. Predefined heads are
    excluded by the guard (a predefined `.op` types through `AppSpine.op`, which never reads `Ψ`). -/
theorem hasSimpType_fnOps_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false → p ∈ Ψ := by
  match he with
  | .const c _ => intro p hp; simp only [exprFnOps, List.not_mem_nil] at hp
  | .bvar i t _ _ => intro p hp; simp only [exprFnOps, List.not_mem_nil] at hp
  | .app fn arg rty hspine => exact appSpine_fnOps_mem hspine
  | .fvarNullary f t rty hspine => intro p hp; simp only [exprFnOps, List.not_mem_nil] at hp
  | .ite c t t' d hc ht he_ =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_append] at hp
    rcases hp with (h | h) | h
    · exact hasSimpType_fnOps_mem hc p h hnpre
    · exact hasSimpType_fnOps_mem ht p h hnpre
    · exact hasSimpType_fnOps_mem he_ p h hnpre
  | .eq e1 e2 t _ he1 he2 =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_append] at hp
    rcases hp with h | h
    · exact hasSimpType_fnOps_mem he1 p h hnpre
    · exact hasSimpType_fnOps_mem he2 p h hnpre
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_append] at hp
    rcases hp with h | h
    · exact hasSimpType_fnOps_mem htr p h hnpre
    · exact hasSimpType_fnOps_mem hbody p h hnpre
theorem appSpine_fnOps_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false → p ∈ Ψ := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_append] at hp
    rcases hp with h | h
    · exact appSpine_fnOps_mem hrest p h hnpre
    · exact hasSimpType_fnOps_mem harg p h hnpre
  | .fvar f t acc' rty _ _ _ => intro p hp; simp only [exprFnOps, List.not_mem_nil] at hp
  | .op o oty acc' rty hop hcol =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_singleton] at hp
    subst hp
    have hpre : isPredefinedOp (o.name, oty).1 = true := by
      show isPredefinedOp o.name = true
      unfold isPredefinedOp
      generalize hg : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = co at hop ⊢
      cases hop <;> rfl
    rw [hpre] at hnpre
    exact Bool.noConfusion hnpre
  | .fnOp o oty acc' rty hmem hnpre' hcol hbase =>
    intro p hp hnpre
    simp only [exprFnOps, List.mem_singleton] at hp
    subst hp
    exact hmem
termination_by structural hspine
end

/-- **Alignment of `exprFnOps` with the collection seed `exprFnRefs`.** A NON-`corePredefinedOpToSMTOp`
    op name that appears at an `exprFnOps` head is collected by `exprFnRefs` (they share recursion
    structure; `exprFnRefs` skips exactly the heads `corePredefinedOpToSMTOp` recognizes). Pure structural
    fact — no typing needed. Bridges the closure seed (`exprFnRefs`) to `exprFnOps`. -/
theorem exprFnOps_name_mem_exprFnRefs {uAT : Bool} (e : Expression.Expr) :
    ∀ p ∈ exprFnOps e, corePredefinedOpToSMTOp uAT
        (CoreOp.ofString (Core.NameMangling.demangledBaseName p.1)) = none →
      p.1 ∈ exprFnRefs uAT e := by
  induction e with
  | op _ o oty =>
    intro p hp hnone
    cases oty with
    | none => simp only [exprFnOps, List.not_mem_nil] at hp
    | some oty =>
      simp only [exprFnOps, List.mem_singleton] at hp
      subst hp
      simp only [exprFnRefs, hnone, Option.isSome_none, Bool.false_eq_true, if_false,
        List.mem_singleton]
  | app _ fn arg ihfn iharg =>
    intro p hp hnone
    simp only [exprFnOps, List.mem_append] at hp
    simp only [exprFnRefs, List.mem_append]
    rcases hp with h | h
    · exact Or.inl (ihfn p h hnone)
    · exact Or.inr (iharg p h hnone)
  | ite _ c t e ihc iht ihe =>
    intro p hp hnone
    simp only [exprFnOps, List.mem_append] at hp
    simp only [exprFnRefs, List.mem_append]
    rcases hp with (h | h) | h
    · exact Or.inl (Or.inl (ihc p h hnone))
    · exact Or.inl (Or.inr (iht p h hnone))
    · exact Or.inr (ihe p h hnone)
  | eq _ e1 e2 ih1 ih2 =>
    intro p hp hnone
    simp only [exprFnOps, List.mem_append] at hp
    simp only [exprFnRefs, List.mem_append]
    rcases hp with h | h
    · exact Or.inl (ih1 p h hnone)
    · exact Or.inr (ih2 p h hnone)
  | quant _ _ _ _ tr body ihtr ihbody =>
    intro p hp hnone
    simp only [exprFnOps, List.mem_append] at hp
    simp only [exprFnRefs, List.mem_append]
    rcases hp with h | h
    · exact Or.inl (ihtr p h hnone)
    · exact Or.inr (ihbody p h hnone)
  | abs _ _ _ body ihbody =>
    intro p hp hnone
    simp only [exprFnOps] at hp
    simp only [exprFnRefs]
    exact ihbody p hp hnone
  | const _ _ => intro p hp _; simp only [exprFnOps, List.not_mem_nil] at hp
  | bvar _ _ => intro p hp _; simp only [exprFnOps, List.not_mem_nil] at hp
  | fvar _ _ _ => intro p hp _; simp only [exprFnOps, List.not_mem_nil] at hp

/-! ## Well-typed expressions collect only non-predefined (tier-2 user-function) names -/

/-- A non-`isPredefinedOp` name is not recognised by `corePredefinedOpToSMTOp` either (both classify on the
    demangled base name via `CoreOp.ofString`; `isPredefinedOp` false ⇒ `.other` ⇒ the `_ => none` arm). -/
theorem corePredefinedOp_none_of_notPredefined {uAT : Bool} {name : String}
    (h : isPredefinedOp name = false) :
    corePredefinedOpToSMTOp uAT (CoreOp.ofString (Core.NameMangling.demangledBaseName name)) = none := by
  have hother : ∃ s, CoreOp.ofString (Core.NameMangling.demangledBaseName name) = .other s := by
    unfold isPredefinedOp at h
    split at h
    · rename_i s heq; exact ⟨s, heq⟩
    · simp at h
  obtain ⟨s, hs⟩ := hother
  rw [hs]; rfl

mutual
/-- **A typed expression's collected fn-refs are non-predefined.** Every `nm ∈ exprFnRefs uAT e` of a
    well-typed `e` has `isPredefinedOp nm = false`. `exprFnRefs` collects a head only when
    `corePredefinedOpToSMTOp = none`; in a typed `e` such a head is typed via `AppSpine.fnOp` (which
    demands `isPredefinedOp = false`), never `AppSpine.op` (whose `CoreOpHasType` heads are all
    `corePredefinedOpToSMTOp = some`, so `exprFnRefs` skips them). -/
theorem hasSimpType_exprFnRefs_notPredefined {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy} (uAT : Bool) (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
  match he with
  | .const c _ => intro nm hnm; simp only [exprFnRefs, List.not_mem_nil] at hnm
  | .bvar i t _ _ => intro nm hnm; simp only [exprFnRefs, List.not_mem_nil] at hnm
  | .app fn arg rty hspine => exact appSpine_exprFnRefs_notPredefined uAT hspine
  | .fvarNullary f t rty hspine => intro nm hnm; simp only [exprFnRefs, List.not_mem_nil] at hnm
  | .ite c t t' d hc ht he_ =>
    intro nm hnm
    simp only [exprFnRefs, List.mem_append] at hnm
    rcases hnm with (h | h) | h
    · exact hasSimpType_exprFnRefs_notPredefined uAT hc nm h
    · exact hasSimpType_exprFnRefs_notPredefined uAT ht nm h
    · exact hasSimpType_exprFnRefs_notPredefined uAT he_ nm h
  | .eq e1 e2 t _ he1 he2 =>
    intro nm hnm
    simp only [exprFnRefs, List.mem_append] at hnm
    rcases hnm with h | h
    · exact hasSimpType_exprFnRefs_notPredefined uAT he1 nm h
    · exact hasSimpType_exprFnRefs_notPredefined uAT he2 nm h
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    intro nm hnm
    simp only [exprFnRefs, List.mem_append] at hnm
    rcases hnm with h | h
    · exact hasSimpType_exprFnRefs_notPredefined uAT htr nm h
    · exact hasSimpType_exprFnRefs_notPredefined uAT hbody nm h
theorem appSpine_exprFnRefs_notPredefined {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy} (uAT : Bool)
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    intro nm hnm
    simp only [exprFnRefs, List.mem_append] at hnm
    rcases hnm with h | h
    · exact appSpine_exprFnRefs_notPredefined uAT hrest nm h
    · exact hasSimpType_exprFnRefs_notPredefined uAT harg nm h
  | .fvar f t acc' rty _ _ _ => intro nm hnm; simp only [exprFnRefs, List.not_mem_nil] at hnm
  | .op o oty acc' rty hop hcol =>
    intro nm hnm
    exfalso
    have hsome : (corePredefinedOpToSMTOp uAT
        (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name))).isSome = true := by
      generalize hg : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = co at hop ⊢
      cases hop <;> rfl
    simp only [exprFnRefs, hsome, if_true, List.not_mem_nil] at hnm
  | .fnOp o oty acc' rty hmem hnpre' hcol hbase =>
    intro nm hnm
    have hnone : corePredefinedOpToSMTOp uAT
        (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) = none :=
      corePredefinedOp_none_of_notPredefined hnpre'
    simp only [exprFnRefs, hnone, Option.isSome_none, Bool.false_eq_true, if_false,
      List.mem_singleton] at hnm
    subst hnm
    exact hnpre'
termination_by structural hspine
end

/-! ## Well-typed expressions' free variables are all in the free-var context `Φ` -/

mutual
/-- Every free variable of a well-typed expression is declared in `Φ` (the only positive use of `Φ` is
    `AppSpine.fvar`, which demands `(f.name, τ) ∈ Φ`). -/
theorem hasSimpType_freeVars_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) :
    ∀ p ∈ LExpr.freeVars e, p.1.name ∈ Φ.map Prod.fst := by
  match he with
  | .const c _ => intro p hp; simp only [LExpr.freeVars, List.not_mem_nil] at hp
  | .bvar i t _ _ => intro p hp; simp only [LExpr.freeVars, List.not_mem_nil] at hp
  | .app fn arg rty hspine => exact appSpine_freeVars_mem hspine
  | .fvarNullary f t rty hspine => exact appSpine_freeVars_mem hspine
  | .ite c t t' d hc ht he_ =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp
    rcases hp with (h | h) | h
    · exact hasSimpType_freeVars_mem hc p h
    · exact hasSimpType_freeVars_mem ht p h
    · exact hasSimpType_freeVars_mem he_ p h
  | .eq e1 e2 t _ he1 he2 =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp
    rcases hp with h | h
    · exact hasSimpType_freeVars_mem he1 p h
    · exact hasSimpType_freeVars_mem he2 p h
  | .quant qty qbody qk qname qtr qτtr _ htr hbody =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp
    rcases hp with h | h
    · exact hasSimpType_freeVars_mem htr p h
    · exact hasSimpType_freeVars_mem hbody p h
theorem appSpine_freeVars_mem {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    ∀ p ∈ LExpr.freeVars e, p.1.name ∈ Φ.map Prod.fst := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp
    rcases hp with h | h
    · exact appSpine_freeVars_mem hrest p h
    · exact hasSimpType_freeVars_mem harg p h
  | .fvar f τ acc' rty hmem hcol hbase =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_singleton] at hp
    subst hp
    exact List.mem_map.mpr ⟨(f.name, τ), hmem, rfl⟩
  | .op o oty acc' rty hop hcol => intro p hp; simp only [LExpr.freeVars, List.not_mem_nil] at hp
  | .fnOp o oty acc' rty hmem hnpre hcol hbase =>
    intro p hp; simp only [LExpr.freeVars, List.not_mem_nil] at hp
termination_by structural hspine
end

/-! ## Reachability-walk invariants (the manual discharge of the closure gap) -/

/-- `collectFuncsGo` only ever grows `seenFns`. -/
theorem collectFuncsGo_seenFns_mono {uAT : Bool} {F : Lambda.Factory CoreLParams} {dtOps : List String} :
    ∀ (st : CollectState) (wl : List String) {nm : String},
      nm ∈ st.seenFns → nm ∈ (collectFuncsGo uAT F dtOps st wl).seenFns := by
  intro st wl
  fun_induction collectFuncsGo uAT F dtOps st wl with
  | case1 st => intro nm h; exact h
  | case2 st name rest hnone ih => intro nm h; exact ih h
  | case3 st name rest f hsome hcond ih => intro nm h; exact ih h
  | case4 st name rest f hsome hcond ih =>
      intro nm h
      exact ih (by simp only [CollectState.markFuncSeen, List.mem_append, List.mem_singleton]; exact Or.inl h)

/-- `addFunc f` adds `f`'s name to the function context `toΨ`. -/
theorem addFunc_self_mem_toΨ (st : CollectState) (f : LFunc CoreLParams) :
    f.name.name ∈ ((st.addFunc f).ctx.toΨ).map Prod.fst := by
  unfold CollectState.addFunc
  split <;> simp [CoreCtx.toΨ]

/-- `addFunc` only grows the `toΨ` name set. -/
theorem addFunc_toΨ_mono (st : CollectState) (f : LFunc CoreLParams) {nm : String}
    (h : nm ∈ (st.ctx.toΨ).map Prod.fst) : nm ∈ ((st.addFunc f).ctx.toΨ).map Prod.fst := by
  unfold CollectState.addFunc
  split
  · simp only [CoreCtx.toΨ, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_map, List.mem_cons] at h ⊢
    rcases h with hd | hd <;> simp [hd]
  · simp only [CoreCtx.toΨ, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_map, List.mem_cons] at h ⊢
    rcases h with hd | hd <;> simp [hd]

/-- The materialize fold only grows the `toΨ` name set. -/
theorem foldl_matStep_toΨ_mono :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState) {nm : String},
      nm ∈ (st.ctx.toΨ).map Prod.fst →
      nm ∈ ((l.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
        st).ctx.toΨ).map Prod.fst := by
  intro l
  induction l with
  | nil => intro st nm h; exact h
  | cons g gs ih =>
      intro st nm h
      rw [List.foldl_cons]
      apply ih
      split
      · exact addFunc_toΨ_mono st g h
      · exact h

/-- Every factory function whose name the walk reached (`∈ seenFns`) is materialized into `toΨ`. `seenFns`
    is invariant under the materialize fold, so a function's guard stays satisfied when it is reached. -/
theorem foldl_matStep_mem_toΨ :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState) {f : LFunc CoreLParams},
      f ∈ l → f.name.name ∈ st.seenFns →
      f.name.name ∈ ((l.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
        st).ctx.toΨ).map Prod.fst := by
  intro l
  induction l with
  | nil => intro st f hf hseen; simp at hf
  | cons g gs ih =>
      intro st f hf hseen
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hf with rfl | hmem
      · have hc : st.seenFns.contains f.name.name = true := by
          simp only [List.contains_eq_mem, decide_eq_true_eq]; exact hseen
        simp only [hc, if_true]
        exact foldl_matStep_toΨ_mono gs (st.addFunc f) (addFunc_self_mem_toΨ st f)
      · have hseen' : f.name.name ∈ (if st.seenFns.contains g.name.name then st.addFunc g else st).seenFns := by
          split <;> exact hseen
        exact ih _ hmem hseen'

theorem materializeFuncs_mem_toΨ (st : CollectState) (F : Lambda.Factory CoreLParams)
    {f : LFunc CoreLParams} (hf : f ∈ F.toArray) (hseen : f.name.name ∈ st.seenFns) :
    f.name.name ∈ ((st.materializeFuncs F).ctx.toΨ).map Prod.fst := by
  unfold CollectState.materializeFuncs
  rw [← Array.foldl_toList]
  exact foldl_matStep_mem_toΨ F.toArray.toList st (Array.mem_toList_iff.mpr hf) hseen

/-- **Worklist reachability**: every worklist name that is a real (non-datatype-op) factory function ends
    up in `seenFns` after the walk. -/
theorem collectFuncsGo_worklist_seen {uAT : Bool} {F : Lambda.Factory CoreLParams} {dtOps : List String} :
    ∀ (st : CollectState) (wl : List String) {nm : String},
      nm ∈ wl → (F[nm]?).isSome → Core.NameMangling.demangledBaseName nm ∉ dtOps →
      nm ∈ (collectFuncsGo uAT F dtOps st wl).seenFns := by
  intro st wl
  fun_induction collectFuncsGo uAT F dtOps st wl with
  | case1 st => intro nm hmem _ _; simp at hmem
  | case2 st name rest hnone ih =>
      intro nm hmem hsome hdt
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [hnone] at hsome; simp at hsome
      · exact ih hmem' hsome hdt
  | case3 st name rest f hsome' hcond ih =>
      intro nm hmem hsome hdt
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rcases hcond with hd | hs
        · exact absurd hd hdt
        · exact collectFuncsGo_seenFns_mono st rest hs
      · exact ih hmem' hsome hdt
  | case4 st name rest f hsome' hcond ih =>
      intro nm hmem hsome hdt
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact collectFuncsGo_seenFns_mono (st.markFuncSeen nm) _
          (by simp [CollectState.markFuncSeen])
      · exact ih (List.mem_append.mpr (Or.inr hmem')) hsome hdt

/-- **Seed reachability**: `collectFuncs` sees every `exprFnRefs` seed that is a real factory function. -/
theorem collectFuncs_seeds {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (st : CollectState) (e : Expression.Expr) {nm : String}
    (hnm : nm ∈ exprFnRefs uAT e) (hsome : (F[nm]?).isSome)
    (hdt : Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf) :
    nm ∈ (collectFuncs uAT F tf st e).seenFns := by
  unfold collectFuncs
  exact collectFuncsGo_worklist_seen st (exprFnRefs uAT e) hnm hsome hdt

/-- **Edge closure** (the worklist invariant): if every seen factory function's `funcFnRefs` edges are
    already `∈ seenFns ∨ ∈ worklist`, then after the walk the final `seenFns` is closed under those edges. -/
theorem collectFuncsGo_closed {uAT : Bool} {F : Lambda.Factory CoreLParams} {dtOps : List String} :
    ∀ (st : CollectState) (wl : List String),
      (∀ (g : LFunc CoreLParams), g ∈ F.toArray → g.name.name ∈ st.seenFns →
        ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome → Core.NameMangling.demangledBaseName h ∉ dtOps →
          h ∈ st.seenFns ∨ h ∈ wl) →
      ∀ (g : LFunc CoreLParams), g ∈ F.toArray →
        g.name.name ∈ (collectFuncsGo uAT F dtOps st wl).seenFns →
        ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome → Core.NameMangling.demangledBaseName h ∉ dtOps →
          h ∈ (collectFuncsGo uAT F dtOps st wl).seenFns := by
  intro st wl
  fun_induction collectFuncsGo uAT F dtOps st wl with
  | case1 st =>
      intro hinv g hg hgseen h hh hhsome hhdt
      rcases hinv g hg hgseen h hh hhsome hhdt with h' | h'
      · exact h'
      · simp at h'
  | case2 st name rest hnone ih =>
      intro hinv
      apply ih
      intro g hg hgseen h hh hhsome hhdt
      rcases hinv g hg hgseen h hh hhsome hhdt with h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · rw [hnone] at hhsome; simp at hhsome
        · exact Or.inr h''
  | case3 st name rest f hsome' hcond ih =>
      intro hinv
      apply ih
      intro g hg hgseen h hh hhsome hhdt
      rcases hinv g hg hgseen h hh hhsome hhdt with h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · rcases hcond with hd | hs
          · exact absurd hd hhdt
          · exact Or.inl hs
        · exact Or.inr h''
  | case4 st name rest f hsome' hcond ih =>
      intro hinv
      apply ih
      intro g hg hgseen h hh hhsome hhdt
      simp only [CollectState.markFuncSeen, List.mem_append, List.mem_singleton] at hgseen
      rcases hgseen with hgold | hgname
      · rcases hinv g hg hgold h hh hhsome hhdt with h' | h'
        · exact Or.inl (by simp only [CollectState.markFuncSeen]; exact List.mem_append.mpr (Or.inl h'))
        · rcases List.mem_cons.mp h' with rfl | h''
          · exact Or.inl (by simp [CollectState.markFuncSeen])
          · exact Or.inr (List.mem_append.mpr (Or.inr h''))
      · have hgf : g = f := by
          obtain ⟨hs, heq⟩ := Factory.mem_name_eq_getElem hg hgname
          rw [← heq]
          exact Factory.getElem?_some_getElem hsome'
        subst hgf
        exact Or.inr (List.mem_append.mpr (Or.inl hh))

/-! ## `exprFnRefs` is invariant under `funcBvarSubst` lifting (function-body edge route) -/

/-- `liftBVars` only shifts bvar indices; it preserves every `.op` head, so the collected fn-refs are
    unchanged. -/
theorem exprFnRefs_liftBVars (uAT : Bool) (n : Nat) (e : Expression.Expr) (c : Nat) :
    exprFnRefs uAT (LExpr.liftBVars n e c) = exprFnRefs uAT e := by
  induction e generalizing c with
  | const | op | fvar => rfl
  | bvar m i => simp only [LExpr.liftBVars]; split <;> rfl
  | abs _ _ _ _ ih => simp only [LExpr.liftBVars, exprFnRefs]; exact ih (c + 1)
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.liftBVars, exprFnRefs]; rw [iht (c + 1), ihb (c + 1)]
  | app _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1 c, ih2 c]
  | ite _ _ _ _ ih1 ih2 ih3 => simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1 c, ih2 c, ih3 c]
  | eq _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, exprFnRefs]; rw [ih1 c, ih2 c]

/-- `Map.find?` returns a value present in the map's value list. -/
theorem Map.find?_some_mem_snd {α β : Type} [DecidableEq α] {m : Map α β} {k : α} {v : β}
    (h : Map.find? m k = some v) : v ∈ m.map Prod.snd := by
  induction m with
  | nil => simp only [Map.find?] at h; contradiction
  | cons hd tl ih =>
    simp only [Map.find?] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every value of `funcBvarSubst f` is a `.bvar`, so it carries no fn-refs. -/
theorem funcBvarSubst_find_exprFnRefs_nil (uAT : Bool) {f : LFunc CoreLParams}
    {k : CoreLParams.Identifier} {v : Expression.Expr}
    (h : Map.find? (funcBvarSubst f) k = some v) : exprFnRefs uAT v = [] := by
  have hmem := Map.find?_some_mem_snd h
  have hfb : funcBvarSubst f
      = List.map (fun i => (f.inputs.keys[i]!, (LExpr.bvar () i : Expression.Expr)))
          (List.range f.inputs.length) := rfl
  rw [hfb, List.map_map] at hmem
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
  rw [← hi]; rfl

/-- Worker: `exprFnRefs` is unchanged by `substFvarsLifting.go` when every replaced fvar maps to an
    fn-ref-free expression (true for `funcBvarSubst`, whose values are bvars). -/
theorem exprFnRefs_substFvarsLifting_go (uAT : Bool)
    (sm : Map CoreLParams.Identifier Expression.Expr)
    (hsm : ∀ k v, Map.find? sm k = some v → exprFnRefs uAT v = []) :
    ∀ (e : Expression.Expr) (depth : Nat),
      exprFnRefs uAT (LExpr.substFvarsLifting.go sm e depth) = exprFnRefs uAT e := by
  intro e
  induction e with
  | const | op | bvar => intro depth; rfl
  | fvar m x ty =>
    intro depth
    have hrhs : exprFnRefs uAT (LExpr.fvar m x ty) = [] := rfl
    rw [hrhs]
    simp only [LExpr.substFvarsLifting.go]
    cases hf : Map.find? sm x with
    | none => rfl
    | some v => rw [exprFnRefs_liftBVars]; exact hsm x v hf
  | abs _ _ _ _ ih => intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; exact ih (depth + 1)
  | quant _ _ _ _ _ _ iht ihb =>
    intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [iht (depth + 1), ihb (depth + 1)]
  | app _ _ _ ih1 ih2 => intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1 depth, ih2 depth]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1 depth, ih2 depth, ih3 depth]
  | eq _ _ _ ih1 ih2 => intro depth; simp only [LExpr.substFvarsLifting.go, exprFnRefs]; rw [ih1 depth, ih2 depth]

/-- `exprFnRefs (substFvarsLifting body (funcBvarSubst f)) = exprFnRefs body` — the bvar-substitution the
    materializer applies to a define-fun body preserves the collected fn-refs. -/
theorem exprFnRefs_substFvarsLifting_funcBvarSubst (uAT : Bool) (f : LFunc CoreLParams)
    (body : Expression.Expr) :
    exprFnRefs uAT (LExpr.substFvarsLifting body (funcBvarSubst f)) = exprFnRefs uAT body := by
  unfold LExpr.substFvarsLifting
  split
  · rfl
  · exact exprFnRefs_substFvarsLifting_go uAT (funcBvarSubst f)
      (fun k v hkv => funcBvarSubst_find_exprFnRefs_nil uAT hkv) body 0

/-! ## `seen ⟹ nonPredefined`: the walk only ever marks tier-2 user-function names -/

/-- Extract the (bvar-lifted) body typing of a non-recursive factory function from `FactoryFnsWF`
    (the `Ψ` is the callee-before-caller prefix at `f`'s position; irrelevant to the op-heads). -/
theorem FactoryFnsWF.mem_hasSimpType {Ψ0 : FnCtx} {fns : List (LFunc CoreLParams)}
    (h : FactoryFnsWF Ψ0 fns) :
    ∀ f ∈ fns, ∀ body, f.isRecursive = false → f.body = some body →
      ∃ Ψ, LExpr.HasSimpType [] Ψ f.inputs.values
          (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output ∧
        (∀ q ∈ Ψ, q ∈ Ψ0 ∨
          q ∈ fns.map (fun g => (g.name.name, LMonoTy.mkArrow' g.output g.inputs.values))) := by
  induction h with
  | nil => intro f hf; simp at hf
  | @cons Ψ f rest hbody _ ih =>
    intro g hg body hrec hb
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Ψ, hbody body hrec hb, fun q hq => Or.inl hq⟩
    · obtain ⟨Ψ', hty, hsub⟩ := ih g hg body hrec hb
      refine ⟨Ψ', hty, fun q hq => ?_⟩
      rcases hsub q hq with hq' | hq'
      · rw [List.mem_append, List.mem_singleton] at hq'
        rcases hq' with hq'' | hq''
        · exact Or.inl hq''
        · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inl hq'')
      · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hq')

/-- **Positional** body typing: at a split `fns = pre ++ f :: suf`, `f`'s body is typed against the exact
    threaded prefix `Ψ0 ++ pre.map sig` (the callee-before-caller context). Exposes the "before-`f`"
    position that the reachable-fnDef ordering argument needs. -/
theorem FactoryFnsWF.mem_hasSimpType_pos {Ψ0 : FnCtx} {fns : List (LFunc CoreLParams)}
    (h : FactoryFnsWF Ψ0 fns) :
    ∀ (pre : List (LFunc CoreLParams)) (f : LFunc CoreLParams) (suf : List (LFunc CoreLParams)),
      fns = pre ++ f :: suf → f.isRecursive = false → ∀ body, f.body = some body →
      LExpr.HasSimpType [] (Ψ0 ++ pre.map (fun g => (g.name.name, LMonoTy.mkArrow' g.output g.inputs.values)))
        f.inputs.values (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output := by
  induction h with
  | nil => intro pre f suf heq; simp at heq
  | @cons Ψ d rest hbody hrestWF ih =>
    intro pre f suf heq hrec body hbd
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, _⟩ := heq
      simpa only [List.map_nil, List.append_nil] using hbody body hrec hbd
    | cons d' pre' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq'⟩ := heq
      have := ih pre' f suf heq' hrec body hbd
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using this

/-- Every fn-ref of a `nonPredefined` factory function is itself non-predefined: its axiom refs are typed
    by `fnAxiomsWF`, and (only for non-recursive `f`) its body refs are typed by `fnsWF` — using that
    `exprFnRefs` is invariant under the bvar lift. Recursive bodies are not walked (`funcFnRefs`). -/
theorem funcFnRefs_notPredefined {uAT : Bool} {F : Lambda.Factory CoreLParams}
    (hsimp : Factory.SimpWF F tf) {f : LFunc CoreLParams} (hf : f ∈ Factory.nonPredefined F tf) :
    ∀ nm ∈ funcFnRefs uAT f, isPredefinedOp nm = false := by
  intro nm hnm
  unfold funcFnRefs at hnm
  rw [List.mem_append] at hnm
  rcases hnm with hbody | hax
  · cases hrec : f.isRecursive with
    | true => simp only [hrec, if_true, List.not_mem_nil] at hbody
    | false =>
      cases hb : f.body with
      | none => simp [hrec, hb] at hbody
      | some body =>
        simp only [hrec, hb, Option.map_some, Option.getD_some] at hbody
        obtain ⟨Ψ, hty, _⟩ := hsimp.fnsWF.mem_hasSimpType f hf body hrec hb
        rw [← exprFnRefs_substFvarsLifting_funcBvarSubst uAT f body] at hbody
        exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hbody
  · rw [List.mem_flatMap] at hax
    obtain ⟨e, he, hne⟩ := hax
    exact hasSimpType_exprFnRefs_notPredefined uAT (hsimp.fnAxiomsWF f hf e he) nm hne

/-- **Walk invariant** `seen ⟹ nonPredefined`: if every name already seen and every worklist name is
    non-predefined, then so is every name seen after the walk. Maintained because a newly-dequeued factory
    function is non-predefined (from the worklist invariant), hence in `nonPredefined F tf`, so its pushed
    `funcFnRefs` edges are non-predefined (`funcFnRefs_notPredefined`). -/
theorem collectFuncsGo_seen_notPredefined {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (hsimp : Factory.SimpWF F tf) :
    ∀ (st : CollectState) (wl : List String),
      (∀ nm ∈ st.seenFns, isPredefinedOp nm = false) →
      (∀ nm ∈ wl, isPredefinedOp nm = false) →
      ∀ nm ∈ (collectFuncsGo uAT F (datatypeOpNames tf) st wl).seenFns, isPredefinedOp nm = false := by
  intro st wl
  fun_induction collectFuncsGo uAT F (datatypeOpNames tf) st wl with
  | case1 st => intro hseen _ nm h; exact hseen nm h
  | case2 st name rest hnone ih =>
      intro hseen hwl; exact ih hseen (fun nm h => hwl nm (List.mem_cons_of_mem _ h))
  | case3 st name rest f hsome hcond ih =>
      intro hseen hwl; exact ih hseen (fun nm h => hwl nm (List.mem_cons_of_mem _ h))
  | case4 st name rest f hsome hcond ih =>
      intro hseen hwl
      apply ih
      · intro nm h
        simp only [CollectState.markFuncSeen, List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact hseen nm h
        · rw [h]; exact hwl name List.mem_cons_self
      · intro nm h
        rw [List.mem_append] at h
        rcases h with h | h
        · have hnamepre : isPredefinedOp name = false := hwl name List.mem_cons_self
          have hfname : f.name.name = name := Factory.getElem?_name hsome
          have hfnon : f ∈ Factory.nonPredefined F tf :=
            mem_nonPredefined.mpr
              ⟨Array.mem_toList_iff.mpr (Factory.getElem?_is_some_implies_mem hsome),
               by rw [hfname]; exact hnamepre,
               by rw [hfname]; exact fun h => hcond (Or.inl h)⟩
          exact funcFnRefs_notPredefined hsimp hfnon nm h
        · exact hwl nm (List.mem_cons_of_mem _ h)

/-! ## Fold of `collectFuncs` over the obligation expressions -/

/-- The fold of `collectFuncs` only grows `seenFns`. -/
theorem foldl_collectFuncs_seenFns_mono {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} :
    ∀ (l : List Expression.Expr) (st : CollectState) {nm : String},
      nm ∈ st.seenFns → nm ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns := by
  intro l
  induction l with
  | nil => intro st nm h; exact h
  | cons e rest ih =>
      intro st nm h
      rw [List.foldl_cons]
      apply ih
      unfold collectFuncs
      exact collectFuncsGo_seenFns_mono st (exprFnRefs uAT e) h

/-- **Fold-level seed reachability**: an `exprFnRefs` seed of any expression in the list ends up seen. -/
theorem foldl_collectFuncs_seed {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} :
    ∀ (l : List Expression.Expr) (st : CollectState) {e : Expression.Expr} {nm : String},
      e ∈ l → nm ∈ exprFnRefs uAT e → (F[nm]?).isSome →
      Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf →
      nm ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns := by
  intro l
  induction l with
  | nil => intro st e nm he _ _ _; simp at he
  | cons e' rest ih =>
      intro st e nm he hnm hsome hdt
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he'
      · apply foldl_collectFuncs_seenFns_mono
        exact collectFuncs_seeds st e hnm hsome hdt
      · exact ih (collectFuncs uAT F tf st e') he' hnm hsome hdt

/-- **Fold-level edge closure**: the fold's `seenFns` is closed under `funcFnRefs` edges of seen functions. -/
theorem foldl_collectFuncs_closed {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} :
    ∀ (l : List Expression.Expr) (st : CollectState),
      (∀ g ∈ F.toArray, g.name.name ∈ st.seenFns →
        ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome →
          Core.NameMangling.demangledBaseName h ∉ datatypeOpNames tf → h ∈ st.seenFns) →
      ∀ g ∈ F.toArray, g.name.name ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns →
        ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome →
          Core.NameMangling.demangledBaseName h ∉ datatypeOpNames tf →
          h ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns := by
  intro l
  induction l with
  | nil => intro st hclosed; exact hclosed
  | cons e rest ih =>
      intro st hclosed
      rw [List.foldl_cons]
      apply ih
      unfold collectFuncs
      exact collectFuncsGo_closed st (exprFnRefs uAT e)
        (fun g hg hgseen h hh hs hd => Or.inl (hclosed g hg hgseen h hh hs hd))

/-- **Fold-level `seen ⟹ nonPredefined`**: if every listed expression's `exprFnRefs` is non-predefined
    (true for well-typed exprs), the fold marks only non-predefined names. -/
theorem foldl_collectFuncs_seen_notPredefined {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (hsimp : Factory.SimpWF F tf) :
    ∀ (l : List Expression.Expr) (st : CollectState),
      (∀ nm ∈ st.seenFns, isPredefinedOp nm = false) →
      (∀ e ∈ l, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false) →
      ∀ nm ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns, isPredefinedOp nm = false := by
  intro l
  induction l with
  | nil => intro st hseen _; exact hseen
  | cons e rest ih =>
      intro st hseen hexprs
      rw [List.foldl_cons]
      apply ih
      · unfold collectFuncs
        exact collectFuncsGo_seen_notPredefined hsimp st (exprFnRefs uAT e) hseen
          (fun nm h => hexprs e List.mem_cons_self nm h)
      · intro e' he' nm h; exact hexprs e' (List.mem_cons_of_mem _ he') nm h

/-- A seen name is never a datatype op — the walk only marks a name seen when it is not in `dtOps`. -/
theorem collectFuncsGo_seen_notDatatypeOp {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} :
    ∀ (st : CollectState) (wl : List String),
      (∀ nm ∈ st.seenFns, Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf) →
      ∀ nm ∈ (collectFuncsGo uAT F (datatypeOpNames tf) st wl).seenFns,
        Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf := by
  intro st wl
  fun_induction collectFuncsGo uAT F (datatypeOpNames tf) st wl with
  | case1 st => intro hseen nm h; exact hseen nm h
  | case2 st name rest hnone ih => intro hseen; exact ih hseen
  | case3 st name rest f hsome hcond ih => intro hseen; exact ih hseen
  | case4 st name rest f hsome hcond ih =>
      intro hseen
      apply ih
      intro nm h
      simp only [CollectState.markFuncSeen, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact hseen nm h
      · rw [h]; exact fun hc => hcond (Or.inl hc)

/-- Fold version of `collectFuncsGo_seen_notDatatypeOp` over the obligation expressions. -/
theorem foldl_collectFuncs_seen_notDatatypeOp {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} :
    ∀ (l : List Expression.Expr) (st : CollectState),
      (∀ nm ∈ st.seenFns, Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf) →
      ∀ nm ∈ (l.foldl (collectFuncs uAT F tf) st).seenFns,
        Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf := by
  intro l
  induction l with
  | nil => intro st hseen; exact hseen
  | cons e rest ih =>
      intro st hseen
      rw [List.foldl_cons]
      apply ih
      unfold collectFuncs
      exact collectFuncsGo_seen_notDatatypeOp st (exprFnRefs uAT e) hseen

/-! ## Bridge helpers: predefined-op classification + factory-name lookup -/

/-- Membership in the factory's user-function name context recovers the underlying factory function. -/
theorem factoryFnCtx_name_mem {F : Lambda.Factory CoreLParams} {name : String}
    (h : name ∈ (factoryFnCtx F tf).map Prod.fst) :
    ∃ f, f ∈ F.toArray ∧ f.name.name = name := by
  simp only [factoryFnCtx, Factory.nonPredefined, List.map_map, List.mem_map, Function.comp] at h
  obtain ⟨f, hf, hfn⟩ := h
  refine ⟨f, ?_, hfn⟩
  have : f ∈ F.toArray.toList := (List.mem_filter.mp hf).1
  exact Array.mem_toList_iff.mp this

/-- A factory-function name resolves in the factory (`F[name]?` is `some`). -/
theorem factory_getElem?_isSome_of_mem {F : Lambda.Factory CoreLParams} {f : LFunc CoreLParams}
    {name : String} (hmem : f ∈ F.toArray) (hname : f.name.name = name) :
    (F[name]?).isSome := by
  obtain ⟨hs, _⟩ := Factory.mem_name_eq_getElem hmem hname
  have hsm : name ∈ F.nameMap := hs
  simp +instances only [Factory.instGetElem?, Factory.get?]
  split
  · rename_i hnone
    have := Std.HashMap.isSome_getElem?_iff_mem.mpr hsm
    rw [hnone] at this; simp at this
  · rfl


/-! ## Reachable name ⟹ collected `toΨ` (materialize + `collectTypes` preservation) -/

/-- `collectObligation` unfolds to the `collectTypes` fold over the materialized reachability state, with
    the `datatypes` field set to the block-regrouped reached datatypes (`seenTypes`). Downstream field
    projections read only NON-`datatypes` fields, which the record update leaves untouched. -/
theorem collectObligation_eq_collectTypesFold (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities)
    (d : Imperative.ProofObligation Expression) :
    collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d
      = { ((obligationExprs d).foldl (collectTypes uAT tf karities)
            ((collectFuncsState uAT F tf d).materializeFuncs F)).ctx with
          datatypes := datatypeBlocksLD tf
            (((obligationExprs d).foldl (collectTypes uAT tf karities)
              ((collectFuncsState uAT F tf d).materializeFuncs F)).seenTypes) } := rfl

/-- The collected `toΨ` names are those materialized after the reachability fold (`collectTypes` touches
    only datatypes/sorts, never `fnDecls`/`fnDefs`). -/
theorem collectObligation_toΨ_map_eq (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities)
    (d : Imperative.ProofObligation Expression) :
    ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst
      = (((collectFuncsState uAT F tf d).materializeFuncs F).ctx.toΨ).map Prod.fst := by
  rw [collectObligation_eq_collectTypesFold]
  exact foldl_ctx_proj (fun c => (c.toΨ).map Prod.fst)
    (fun s e => by
      unfold collectTypes
      exact collectTypesGo_ctx_proj uAT tf karities (fun c => (c.toΨ).map Prod.fst)
        (fun _ _ => rfl) (fun _ _ _ => rfl) s _)
    (obligationExprs d) ((collectFuncsState uAT F tf d).materializeFuncs F)

/-- **Seen ⟹ collected `toΨ`.** A factory function whose name the reachability fold marked seen has its
    name in the collected `toΨ`. -/
theorem seen_mem_collectObligation_toΨ (uAT : Bool) (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) (karities : KnownTypeArities)
    (d : Imperative.ProofObligation Expression) {f : LFunc CoreLParams}
    (hf : f ∈ F.toArray) (hseen : f.name.name ∈ (collectFuncsState uAT F tf d).seenFns) :
    f.name.name ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst := by
  rw [collectObligation_toΨ_map_eq]
  exact materializeFuncs_mem_toΨ (collectFuncsState uAT F tf d) F hf hseen

/-! ## Collected program chunks are among `obligationExprs` -/

/-- The `obligationExprs` flat-map function (assumption/det bodies, distinct members). -/
private def oblExprStep (entry : Imperative.PathConditionEntry Expression) : List Expression.Expr :=
  match entry with
  | .assumption _ e => [e]
  | .varDecl _ _ (.det e) => [e]
  | .varDecl _ _ .nondet => []
  | .distinct _ es => es

/-- The three program chunks accumulated by the obligation-partition fold are covered by the entry
    flat-map (`oblExprStep`), modulo the seed accumulator. -/
theorem foldl_oblStep_chunks_mem :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (c : CoreCtx),
      (∀ e ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).assumptions,
          e ∈ c.assumptions ∨ e ∈ es.flatMap oblExprStep) ∧
      (∀ v ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs,
          v ∈ c.varDefs ∨ v.body ∈ es.flatMap oblExprStep) ∧
      (∀ g ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).distincts,
          g ∈ c.distincts ∨ ∀ e ∈ g, e ∈ es.flatMap oblExprStep) := by
  intro es
  induction es with
  | nil => intro c; exact ⟨fun e h => Or.inl h, fun v h => Or.inl h, fun g h => Or.inl h⟩
  | cons entry rest ih =>
    intro c
    -- Convenience: lift `∈ rest.flatMap` into `∈ (entry :: rest).flatMap`.
    have tailMem : ∀ {x : Expression.Expr}, x ∈ rest.flatMap oblExprStep →
        x ∈ (entry :: rest).flatMap oblExprStep := fun hx => by
      rw [List.flatMap_cons, List.mem_append]; exact Or.inr hx
    have headMem : ∀ {x : Expression.Expr}, x ∈ oblExprStep entry →
        x ∈ (entry :: rest).flatMap oblExprStep := fun hx => by
      rw [List.flatMap_cons, List.mem_append]; exact Or.inl hx
    cases entry with
    | assumption l a =>
      obtain ⟨iha, ihv, ihd⟩ := ih { c with assumptions := c.assumptions ++ [a] }
      refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
      · simp only [List.foldl_cons] at he
        rcases iha e he with h | h
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (headMem (by simp only [oblExprStep, List.mem_singleton]; exact h))
        · exact Or.inr (tailMem h)
      · simp only [List.foldl_cons] at hv
        exact (ihv v hv).imp id tailMem
      · simp only [List.foldl_cons] at hg
        exact (ihd g hg).imp id (fun h e he => tailMem (h e he))
    | varDecl name ty dv =>
      cases dv with
      | det a =>
        cases hm : ty.toMonoType? with
        | none =>
          obtain ⟨iha, ihv, ihd⟩ := ih c
          refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
          · simp only [List.foldl_cons, hm] at he; exact (iha e he).imp id tailMem
          · simp only [List.foldl_cons, hm] at hv; exact (ihv v hv).imp id tailMem
          · simp only [List.foldl_cons, hm] at hg; exact (ihd g hg).imp id (fun h e he => tailMem (h e he))
        | some mty =>
          obtain ⟨iha, ihv, ihd⟩ := ih { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := a }] }
          refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
          · simp only [List.foldl_cons, hm] at he; exact (iha e he).imp id tailMem
          · simp only [List.foldl_cons, hm] at hv
            rcases ihv v hv with h | h
            · simp only [List.mem_append, List.mem_singleton] at h
              rcases h with h | h
              · exact Or.inl h
              · exact Or.inr (headMem (by simp only [oblExprStep, List.mem_singleton, h]))
            · exact Or.inr (tailMem h)
          · simp only [List.foldl_cons, hm] at hg; exact (ihd g hg).imp id (fun h e he => tailMem (h e he))
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          obtain ⟨iha, ihv, ihd⟩ := ih c
          refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
          · simp only [List.foldl_cons, hm] at he; exact (iha e he).imp id tailMem
          · simp only [List.foldl_cons, hm] at hv; exact (ihv v hv).imp id tailMem
          · simp only [List.foldl_cons, hm] at hg; exact (ihd g hg).imp id (fun h e he => tailMem (h e he))
        | some mty =>
          obtain ⟨iha, ihv, ihd⟩ := ih { c with varDecls := c.varDecls ++ [(name.name, mty)] }
          refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
          · simp only [List.foldl_cons, hm] at he; exact (iha e he).imp id tailMem
          · simp only [List.foldl_cons, hm] at hv; exact (ihv v hv).imp id tailMem
          · simp only [List.foldl_cons, hm] at hg; exact (ihd g hg).imp id (fun h e he => tailMem (h e he))
    | distinct l es' =>
      obtain ⟨iha, ihv, ihd⟩ := ih { c with distincts := c.distincts ++ [es'] }
      refine ⟨fun e he => ?_, fun v hv => ?_, fun g hg => ?_⟩
      · simp only [List.foldl_cons] at he; exact (iha e he).imp id tailMem
      · simp only [List.foldl_cons] at hv; exact (ihv v hv).imp id tailMem
      · simp only [List.foldl_cons] at hg
        rcases ihd g hg with h | h
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (fun e he => headMem (by simp only [oblExprStep, h] at he ⊢; exact he))
        · exact Or.inr (fun e he => tailMem (h e he))

/-- Collected assumptions are among `obligationExprs`. -/
theorem base_assumptions_mem_obligationExprs (d : Imperative.ProofObligation Expression) :
    ∀ e ∈ (obligationBaseCtx d).assumptions, e ∈ obligationExprs d := by
  intro e he
  unfold obligationBaseCtx CoreCtx.addObligationEntries at he
  have key := (foldl_oblStep_chunks_mem d.assumptions.flatten {}).1 e he
  rcases key with h | h
  · exact absurd h (by simp)
  · unfold obligationExprs; rw [List.mem_append]; exact Or.inl h

/-- Collected det-var bodies are among `obligationExprs`. -/
theorem base_varDefs_body_mem_obligationExprs (d : Imperative.ProofObligation Expression) :
    ∀ v ∈ (obligationBaseCtx d).varDefs, v.body ∈ obligationExprs d := by
  intro v hv
  unfold obligationBaseCtx CoreCtx.addObligationEntries at hv
  have key := (foldl_oblStep_chunks_mem d.assumptions.flatten {}).2.1 v hv
  rcases key with h | h
  · exact absurd h (by simp)
  · unfold obligationExprs; rw [List.mem_append]; exact Or.inl h

/-- Collected distinct-group members are among `obligationExprs`. -/
theorem base_distincts_mem_obligationExprs (d : Imperative.ProofObligation Expression) :
    ∀ es ∈ (obligationBaseCtx d).distincts, ∀ e ∈ es, e ∈ obligationExprs d := by
  intro es hes e he
  unfold obligationBaseCtx CoreCtx.addObligationEntries at hes
  have key := (foldl_oblStep_chunks_mem d.assumptions.flatten {}).2.2 es hes
  rcases key with h | h
  · exact absurd h (by simp)
  · unfold obligationExprs; rw [List.mem_append]; exact Or.inl (h e he)

/-- Every expression an entry contributes to `obligationExprs` is well-typed against the factory context
    `Ψ` (assumption body `bool`, det-var body its monotype, distinct member the common base type). -/
theorem pathEntriesWF_flatMap_typed {Ψ : FnCtx} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      PathEntriesWF Ψ Φ0 es →
      ∀ entry ∈ es, ∀ e ∈ (match entry with
          | .assumption _ e => [e]
          | .varDecl _ _ (.det e) => [e]
          | .varDecl _ _ .nondet => ([] : List Expression.Expr)
          | .distinct _ es => es),
        ∃ Φ τ, LExpr.HasSimpType Φ Ψ [] e τ := by
  intro es
  induction es with
  | nil => intro Φ0 _ entry hentry; simp at hentry
  | cons entry rest ih =>
    intro Φ0 hwf entry' hentry' e he
    obtain ⟨hpc, hrest⟩ := hwf.consInv
    rcases List.mem_cons.mp hentry' with rfl | hmem
    · cases hpc with
      | assumption ha => simp only [List.mem_singleton] at he; subst he; exact ⟨_, _, ha⟩
      | varDeclDet hmono hbase hty _ _ =>
        simp only [List.mem_singleton] at he; subst he; exact ⟨_, _, hty⟩
      | varDeclNondet _ _ _ _ => simp only [List.not_mem_nil] at he
      | distinct _ hex => obtain ⟨τ, _, hall⟩ := hex; exact ⟨_, τ, hall e he⟩
    · exact ih (stepCtx Φ0 entry) hrest entry' hmem e he

/-- Every `obligationExprs` expression is well-typed against `factoryFnCtx F tf`. -/
theorem obligationExprs_typed {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression} (hwf : ProofObligation.WF F tf d) :
    ∀ e ∈ obligationExprs d, ∃ Φ τ, LExpr.HasSimpType Φ (factoryFnCtx F tf) [] e τ := by
  intro e he
  unfold obligationExprs at he
  rw [List.mem_append] at he
  rcases he with he | he
  · rw [List.mem_flatMap] at he
    obtain ⟨entry, hentry, hin⟩ := he
    exact pathEntriesWF_flatMap_typed d.assumptions.flatten [] hwf.entriesWF entry hentry e hin
  · simp only [List.mem_singleton] at he; subst he
    exact ⟨_, _, hwf.goalWF⟩

/-- **Closure-correspondence for `collectFuncs`.** For every collected expression `e`
    (the goal, program assumption / det-varDef / distinct bodies, reachable factory define-fun bodies,
    reachable factory axioms), every NON-PREDEFINED `.op`-head NAME used in `e` is a NAME of the collected
    reachable function context `cctx.toΨ`.

    This is the soundness of the `collectFuncs` reachability closure, stated NAME-LEVEL: the closure
    tracks a name set `seenFns` and materializes it, so only the name — not the annotation arrow type — is
    directly recovered; the pair is recovered downstream from the typing derivation + factory-name
    functionality. Via the WF's `fnNamesNotPredefined`, a non-`isPredefinedOp` factory-op name is also not
    recognised by `corePredefinedOpToSMTOp`, so `exprFnRefs` (the seed) collects it
    (`exprFnOps_name_mem_exprFnRefs`); the `collectFuncsGo`/`materializeFuncs` worklist reachability
    invariant (`exprFnRefs`-seeds and `funcFnRefs`-edges land in `cctx.toΨ`'s names) then feeds the six
    typing fields via a `HasSimpType` restriction. -/
theorem obligation_fnOps_reachable {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) (hwf : ProofObligation.WF F tf d)
    (hsimp : Factory.SimpWF F tf) :
    (∀ e ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).assumptions,
        ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false →
          p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) ∧
    (∀ v ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).varDefs,
        ∀ p ∈ exprFnOps v.body, isPredefinedOp p.1 = false →
          p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) ∧
    (∀ es ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).distincts,
        ∀ e ∈ es, ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false →
          p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) ∧
    (∀ d' ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDefs,
        ∀ p ∈ exprFnOps d'.body, isPredefinedOp p.1 = false →
          p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) ∧
    (∀ e ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnAxioms,
        ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false →
          p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) ∧
    (∀ p ∈ exprFnOps d.obligation, isPredefinedOp p.1 = false →
        p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst) := by
  -- Shared facts about the reachability-fold state `collectFuncsState uAT F tf d`.
  -- (1) every reachable expression's fn-refs are non-predefined (well-typed obligation exprs).
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  -- (2) seen ⟹ non-predefined.
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  -- (3) the fold state is edge-closed.
  have hclosed : ∀ g ∈ F.toArray, g.name.name ∈ (collectFuncsState uAT F tf d).seenFns →
      ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome →
        Core.NameMangling.demangledBaseName h ∉ datatypeOpNames tf →
        h ∈ (collectFuncsState uAT F tf d).seenFns :=
    foldl_collectFuncs_closed (obligationExprs d) _ (fun g _ hg => absurd hg (by simp))
  -- (4) a seen factory function is `nonPredefined`.
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  -- Seed route: an `exprFnOps` head of a reachable obligation expression lands in `toΨ`.
  have reach_seed : ∀ (e : Expression.Expr), e ∈ obligationExprs d →
      (∃ Φ Δ τ, LExpr.HasSimpType Φ (factoryFnCtx F tf) Δ e τ) →
      ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false →
        p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst := by
    rintro e hein ⟨Φ, Δ, τ, hty⟩ p hp hnpre
    have hpfac : p ∈ factoryFnCtx F tf := hasSimpType_fnOps_mem hty p hp hnpre
    have hp1 : p.1 ∈ (factoryFnCtx F tf).map Prod.fst := List.mem_map.mpr ⟨p, hpfac, rfl⟩
    obtain ⟨g, hg, hgname⟩ := factoryFnCtx_name_mem hp1
    have hsome : (F[p.1]?).isSome := factory_getElem?_isSome_of_mem hg hgname
    have hnone := corePredefinedOp_none_of_notPredefined (uAT := uAT) hnpre
    have hseed : p.1 ∈ exprFnRefs uAT e := exprFnOps_name_mem_exprFnRefs e p hp hnone
    have hdt := factoryFnCtx_notDatatypeOp hp1
    have hpseen : p.1 ∈ (collectFuncsState uAT F tf d).seenFns :=
      foldl_collectFuncs_seed (obligationExprs d) _ hein hseed hsome hdt
    have hmem := seen_mem_collectObligation_toΨ uAT F tf karities d hg (by rw [hgname]; exact hpseen)
    rwa [hgname] at hmem
  -- Edge route: a `factoryFnCtx` head that is a `funcFnRefs` edge of a seen function lands in `toΨ`.
  have reach_edge : ∀ (f : LFunc CoreLParams) (p : String × LMonoTy),
      f ∈ F.toArray → f.name.name ∈ (collectFuncsState uAT F tf d).seenFns →
      p ∈ factoryFnCtx F tf → p.1 ∈ funcFnRefs uAT f →
        p.1 ∈ ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ).map Prod.fst := by
    intro f p hf hfseen hpfac hedge
    have hp1 : p.1 ∈ (factoryFnCtx F tf).map Prod.fst := List.mem_map.mpr ⟨p, hpfac, rfl⟩
    obtain ⟨g, hg, hgname⟩ := factoryFnCtx_name_mem hp1
    have hsome : (F[p.1]?).isSome := factory_getElem?_isSome_of_mem hg hgname
    have hdt := factoryFnCtx_notDatatypeOp hp1
    have hpseen : p.1 ∈ (collectFuncsState uAT F tf d).seenFns := hclosed f hf hfseen p.1 hedge hsome hdt
    have hmem := seen_mem_collectObligation_toΨ uAT F tf karities d hg (by rw [hgname]; exact hpseen)
    rwa [hgname] at hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- assumptions
    intro e he p hp hnpre
    rw [(collectObligation_chunks d).1] at he
    have hein := base_assumptions_mem_obligationExprs d e he
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hwf e hein
    exact reach_seed e hein ⟨Φ, [], τ, hty⟩ p hp hnpre
  · -- varDefs
    intro v hv p hp hnpre
    rw [(collectObligation_chunks d).2.2] at hv
    have hein := base_varDefs_body_mem_obligationExprs d v hv
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hwf v.body hein
    exact reach_seed v.body hein ⟨Φ, [], τ, hty⟩ p hp hnpre
  · -- distincts
    intro es hes e he p hp hnpre
    rw [(collectObligation_chunks d).2.1] at hes
    have hein := base_distincts_mem_obligationExprs d es hes e he
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hwf e hein
    exact reach_seed e hein ⟨Φ, [], τ, hty⟩ p hp hnpre
  · -- fnDefs
    intro d' hd' p hp hnpre
    obtain ⟨f, hf, hfseen, hrec, body, hbody, hdname, hdargs, hdret, hdbody⟩ :=
      collectObligation_fnDefs_mem d d' hd'
    have hfnon := f_nonPred f hf hfseen
    obtain ⟨Ψ', hty', hsub'⟩ := hsimp.fnsWF.mem_hasSimpType f hfnon body hrec hbody
    rw [hdbody] at hp
    have hpΨ' : p ∈ Ψ' := hasSimpType_fnOps_mem hty' p hp hnpre
    have hpfac : p ∈ factoryFnCtx F tf := by
      rcases hsub' p hpΨ' with h | h
      · exact absurd h (by simp)
      · exact h
    have hnone := corePredefinedOp_none_of_notPredefined (uAT := uAT) hnpre
    have hseedbody : p.1 ∈ exprFnRefs uAT (LExpr.substFvarsLifting body (funcBvarSubst f)) :=
      exprFnOps_name_mem_exprFnRefs _ p hp hnone
    rw [exprFnRefs_substFvarsLifting_funcBvarSubst] at hseedbody
    have hedge : p.1 ∈ funcFnRefs uAT f := by
      unfold funcFnRefs
      rw [List.mem_append]; left
      simp only [hrec, hbody, Bool.false_eq_true, if_false, Option.map_some, Option.getD_some]
      exact hseedbody
    exact reach_edge f p hf hfseen hpfac hedge
  · -- fnAxioms
    intro e he p hp hnpre
    obtain ⟨f, hf, hfseen, hfe⟩ := collectObligation_fnAxioms_mem d e he
    have hfnon := f_nonPred f hf hfseen
    have hty := hsimp.fnAxiomsWF f hfnon e hfe
    have hpfac : p ∈ factoryFnCtx F tf := hasSimpType_fnOps_mem hty p hp hnpre
    have hnone := corePredefinedOp_none_of_notPredefined (uAT := uAT) hnpre
    have hseede : p.1 ∈ exprFnRefs uAT e := exprFnOps_name_mem_exprFnRefs e p hp hnone
    have hedge : p.1 ∈ funcFnRefs uAT f := by
      unfold funcFnRefs
      rw [List.mem_append]; right
      rw [List.mem_flatMap]; exact ⟨e, hfe, hseede⟩
    exact reach_edge f p hf hfseen hpfac hedge
  · -- goal
    intro p hp hnpre
    have hein : d.obligation ∈ obligationExprs d := by
      unfold obligationExprs; rw [List.mem_append]
      exact Or.inr (List.mem_singleton.mpr rfl)
    exact reach_seed d.obligation hein ⟨_, [], _, hwf.goalWF⟩ p hp hnpre

/-! ## Support lemmas for the headline proofs (name/free-var/datatype hygiene) -/

/-- The names in a `stepCtx`-fold context come from the seed or from the entries' `.varDecl` names. -/
theorem foldl_stepCtx_names :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (nm : String),
      nm ∈ (es.foldl stepCtx Φ0).map Prod.fst →
      nm ∈ Φ0.map Prod.fst ∨ nm ∈ es.filterMap (fun x => match x with
        | .varDecl name _ _ => some name.name | _ => none) := by
  intro es
  induction es with
  | nil => intro Φ0 nm h; exact Or.inl h
  | cons entry rest ih =>
    intro Φ0 nm h
    rw [List.foldl_cons] at h
    rcases ih (stepCtx Φ0 entry) nm h with h' | h'
    · cases entry with
      | assumption _ _ => exact Or.inl h'
      | varDecl name ty dv =>
        simp only [stepCtx] at h'
        split at h'
        · rw [List.map_cons, List.mem_cons] at h'
          rcases h' with rfl | h'
          · exact Or.inr (List.mem_filterMap.mpr ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inl h'
        · exact Or.inl h'
      | distinct _ _ => exact Or.inl h'
    · obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp h'
      exact Or.inr (List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem _ ha, hfa⟩)

/-- Free variables of the expressions an entry contributes are all managed (declared by some `.varDecl`),
    threading the `stepCtx` context whose names are all managed. -/
theorem pathEntriesWF_freeVars_managed {Ψ : FnCtx} (managed : List String) :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      PathEntriesWF Ψ Φ0 es →
      (∀ p ∈ Φ0, p.1 ∈ managed) →
      (∀ (name : Expression.Ident) ty dv,
        Imperative.PathConditionEntry.varDecl name ty dv ∈ es → name.name ∈ managed) →
      ∀ entry ∈ es, ∀ e ∈ oblExprStep entry, ∀ p ∈ LExpr.freeVars e, p.1.name ∈ managed := by
  intro es
  induction es with
  | nil => intro Φ0 _ _ _ entry hentry; simp at hentry
  | cons entry rest ih =>
    intro Φ0 hwf hΦ0 hvd entry' hentry' e he p hp
    obtain ⟨hpc, hrest⟩ := hwf.consInv
    rcases List.mem_cons.mp hentry' with rfl | hmem
    · cases hpc with
      | assumption ha =>
        simp only [oblExprStep, List.mem_singleton] at he; subst he
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hasSimpType_freeVars_mem ha p hp)
        rw [← hqe]; exact hΦ0 q hq
      | varDeclDet hmono hbase hty _ _ =>
        simp only [oblExprStep, List.mem_singleton] at he; subst he
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hasSimpType_freeVars_mem hty p hp)
        rw [← hqe]; exact hΦ0 q hq
      | varDeclNondet _ _ _ _ => simp only [oblExprStep, List.not_mem_nil] at he
      | distinct _ hex =>
        obtain ⟨τ, _, hall⟩ := hex
        simp only [oblExprStep] at he
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hasSimpType_freeVars_mem (hall e he) p hp)
        rw [← hqe]; exact hΦ0 q hq
    · refine ih (stepCtx Φ0 entry) hrest ?_ ?_ entry' hmem e he p hp
      · intro q hq
        cases entry with
        | assumption _ _ => exact hΦ0 q hq
        | varDecl name ty dv =>
          simp only [stepCtx] at hq
          split at hq
          · rcases List.mem_cons.mp hq with rfl | hq'
            · exact hvd name ty dv List.mem_cons_self
            · exact hΦ0 q hq'
          · exact hΦ0 q hq
        | distinct _ _ => exact hΦ0 q hq
      · intro name ty dv hin; exact hvd name ty dv (List.mem_cons_of_mem _ hin)

/-- Every free variable appearing in an `obligationExprs` expression is managed. -/
theorem obligationExprs_freeVars_managed {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression} (hpwf : ProofObligation.WF F tf d) :
    ∀ e ∈ obligationExprs d, ∀ p ∈ LExpr.freeVars e, p.1.name ∈ managedNames d := by
  intro e he p hp
  unfold obligationExprs at he
  rw [List.mem_append] at he
  rcases he with he | he
  · rw [List.mem_flatMap] at he
    obtain ⟨entry, hentry, hin⟩ := he
    refine pathEntriesWF_freeVars_managed (managedNames d) d.assumptions.flatten []
      hpwf.entriesWF (by simp) ?_ entry hentry e hin p hp
    intro name ty dv hin'
    exact List.mem_filterMap.mpr ⟨_, hin', rfl⟩
  · simp only [List.mem_singleton] at he; subst he
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hasSimpType_freeVars_mem hpwf.goalWF p hp)
    rcases foldl_stepCtx_names d.assumptions.flatten [] q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩) with h | h
    · simp at h
    · rw [← hqe]; exact h

/-- A `List.foldl` whose step leaves the accumulator unchanged on every list element equals its seed. -/
theorem foldl_eq_init_of_step_id {α β : Type} (f : β → α → β) :
    ∀ (l : List α) (init : β), (∀ b, ∀ a ∈ l, f b a = b) → l.foldl f init = init := by
  intro l
  induction l with
  | nil => intro init _; rfl
  | cons x rest ih =>
    intro init h
    rw [List.foldl_cons, h init x List.mem_cons_self]
    exact ih init (fun b a ha => h b a (List.mem_cons_of_mem _ ha))

/-- Under `ProofObligation.WF`, the obligation has no unmanaged free variables: WF types every obligation
    expression against the `[]`-seeded free-var context, so every `.fvar` head is a path-declared
    (managed) var — hence `unmanagedFVars d` (the un-managed ones) is empty. -/
theorem unmanagedFVars_eq_nil_of_WF {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression} (hpwf : ProofObligation.WF F tf d) :
    unmanagedFVars d = [] := by
  unfold unmanagedFVars
  apply foldl_eq_init_of_step_id
  intro acc x hx
  obtain ⟨ident, ty?⟩ := x
  cases ty? with
  | none => rfl
  | some ty =>
    rw [List.mem_flatMap] at hx
    obtain ⟨e, he, hpe⟩ := hx
    have hman : ident.name ∈ managedNames d := obligationExprs_freeVars_managed hpwf e he (ident, some ty) hpe
    have hc : (managedNames d).contains ident.name = true := by
      simp only [List.contains_eq_mem, decide_eq_true_eq]; exact hman
    simp only [hc, Bool.true_or, if_true]

/-- A base monotype mentions no (non-builtin) type names. -/
theorem tyNameRefs_of_base {uAT : Bool} {τ : LMonoTy} (h : LExpr.MonoTyIsBase τ) :
    tyNameRefs uAT τ = [] := by
  cases h <;> simp [tyNameRefs, isBuiltinTyName]

/-- If a type's `collectArrowTy` splits into base argument types and a base return type, it mentions no
    (non-builtin) type names — its only structure is `arrow` (builtin) over base leaves. -/
theorem tyNameRefs_nil_of_collectArrowTy_base (uAT : Bool) :
    ∀ (τ : LMonoTy) {acc : List LMonoTy} {rty : LMonoTy}, collectArrowTy τ = (acc, rty) →
      (∀ a ∈ acc, LExpr.MonoTyIsBase a) → LExpr.MonoTyIsBase rty → tyNameRefs uAT τ = [] := by
  intro τ
  fun_induction collectArrowTy τ with
  | case1 t1 t2 atys rty' heq ih =>
    intro acc rty hcol hacc hrty
    simp only [Prod.mk.injEq] at hcol
    obtain ⟨hacc_eq, hrty_eq⟩ := hcol
    subst hacc_eq; subst hrty_eq
    have ht1 : LExpr.MonoTyIsBase t1 := hacc t1 List.mem_cons_self
    have htail : ∀ a ∈ atys, LExpr.MonoTyIsBase a := fun a ha => hacc a (List.mem_cons_of_mem _ ha)
    have ht2 : tyNameRefs uAT t2 = [] := ih heq htail hrty
    simp [tyNameRefs, isBuiltinTyName, tyNameRefs_of_base ht1, ht2]
  | case2 τ' hne =>
    intro acc rty hcol hacc hrty
    simp only [Prod.mk.injEq] at hcol
    obtain ⟨_, hrty_eq⟩ := hcol
    subst hrty_eq
    exact tyNameRefs_of_base hrty

/-- Every `CoreOpHasType` operator has base argument and return types (they are all int/bool). -/
theorem coreOpHasType_base {cop : CoreOp} {acc : List LMonoTy} {rty : LMonoTy}
    (h : LExpr.CoreOpHasType cop acc rty) :
    (∀ a ∈ acc, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase rty := by
  cases h <;>
    exact ⟨fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_self, or_false] at ha
      subst ha; constructor, by constructor⟩

/-- `mkArrow'` is the `foldr`-arrow used by `addFunc`'s declared signatures. -/
theorem mkArrow'_eq_foldr (ret : LMonoTy) (args : List LMonoTy) :
    LMonoTy.mkArrow' ret args = List.foldr LMonoTy.arrow ret args := by
  induction args with
  | nil => rfl
  | cons a rest ih => simp only [LMonoTy.mkArrow', List.foldr_cons, ih]

/-- An iterated arrow over base argument/return types mentions no (non-builtin) type names. -/
theorem tyNameRefs_mkArrow'_base (uAT : Bool) :
    ∀ (args : List LMonoTy) (ret : LMonoTy), (∀ a ∈ args, LExpr.MonoTyIsBase a) →
      LExpr.MonoTyIsBase ret → tyNameRefs uAT (LMonoTy.mkArrow' ret args) = [] := by
  intro args
  induction args with
  | nil => intro ret _ hret; simpa [LMonoTy.mkArrow'] using tyNameRefs_of_base hret
  | cons a rest ih =>
    intro ret hargs hret
    have ha : LExpr.MonoTyIsBase a := hargs a List.mem_cons_self
    have hrest : ∀ x ∈ rest, LExpr.MonoTyIsBase x := fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    simp [LMonoTy.mkArrow', LMonoTy.arrow, tyNameRefs, isBuiltinTyName,
      tyNameRefs_of_base ha, ih ret hrest hret]

/-- Every signature in `factoryFnCtx F tf` is a base-typed arrow, so it mentions no (non-builtin) type name. -/
theorem factoryFnCtx_annot_nil {uAT : Bool} {F : Lambda.Factory CoreLParams} (hsimp : Factory.SimpWF F tf) :
    ∀ p ∈ factoryFnCtx F tf, tyNameRefs uAT p.2 = [] := by
  intro p hp
  simp only [factoryFnCtx, List.mem_map] at hp
  obtain ⟨f, hf, hfe⟩ := hp
  subst hfe
  have hsig := hsimp.fnsSigSimp f hf
  exact tyNameRefs_mkArrow'_base uAT f.inputs.values f.output hsig.fnArgsBase hsig.fnRetBase

/-! ## Well-typed expressions reference no (non-builtin) type names (base-only fragment) -/

mutual
/-- A well-typed expression mentions no non-builtin type name, given both typing contexts are base-typed
    (`Φ` from `varDecl` base types, `Ψ` from `factoryFnCtx` base sigs). -/
theorem hasSimpType_exprTypeRefs_nil {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy} (uAT : Bool)
    (hΦ : ∀ p ∈ Φ, tyNameRefs uAT p.2 = []) (hΨ : ∀ p ∈ Ψ, tyNameRefs uAT p.2 = [])
    (he : LExpr.HasSimpType Φ Ψ Δ e τ) : exprTypeRefs uAT e = [] := by
  match he with
  | .const c _ => rfl
  | .bvar i t _ _ => rfl
  | .app fn arg rty hspine => exact appSpine_exprTypeRefs_nil uAT hΦ hΨ hspine
  | .fvarNullary f t rty hspine => exact appSpine_exprTypeRefs_nil uAT hΦ hΨ hspine
  | .ite c t t' d hc ht he_ =>
    simp only [exprTypeRefs, hasSimpType_exprTypeRefs_nil uAT hΦ hΨ hc,
      hasSimpType_exprTypeRefs_nil uAT hΦ hΨ ht, hasSimpType_exprTypeRefs_nil uAT hΦ hΨ he_,
      List.append_nil]
  | .eq e1 e2 t _ he1 he2 =>
    simp only [exprTypeRefs, hasSimpType_exprTypeRefs_nil uAT hΦ hΨ he1,
      hasSimpType_exprTypeRefs_nil uAT hΦ hΨ he2, List.append_nil]
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
    simp only [exprTypeRefs, Option.map_some, Option.getD_some, tyNameRefs_of_base hbase,
      hasSimpType_exprTypeRefs_nil uAT hΦ hΨ htr, hasSimpType_exprTypeRefs_nil uAT hΦ hΨ hbody,
      List.append_nil]
theorem appSpine_exprTypeRefs_nil {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy} (uAT : Bool)
    (hΦ : ∀ p ∈ Φ, tyNameRefs uAT p.2 = []) (hΨ : ∀ p ∈ Ψ, tyNameRefs uAT p.2 = [])
    (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) : exprTypeRefs uAT e = [] := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest =>
    simp only [exprTypeRefs, appSpine_exprTypeRefs_nil uAT hΦ hΨ hrest,
      hasSimpType_exprTypeRefs_nil uAT hΦ hΨ harg, List.append_nil]
  | .fvar f τ acc' rty hmem hcol hbase =>
    simp only [exprTypeRefs, Option.map_some, Option.getD_some]
    exact hΦ (f.name, τ) hmem
  | .op o oty acc' rty hop hcol =>
    simp only [exprTypeRefs, Option.map_some, Option.getD_some]
    obtain ⟨hacc, hrty⟩ := coreOpHasType_base hop
    exact tyNameRefs_nil_of_collectArrowTy_base uAT oty hcol hacc hrty
  | .fnOp o oty acc' rty hmem hnpre hcol hbase =>
    simp only [exprTypeRefs, Option.map_some, Option.getD_some]
    exact hΨ (o.name, oty) hmem
termination_by structural hspine
end

/-! ## `fnDecls` correspondence (for the datatype-free type-seed argument) -/

/-- Every `fnDecl` produced by one `addFunc` is either already present or `f`'s declared arrow signature. -/
theorem addFunc_fnDecls_mem (st : CollectState) (f : LFunc CoreLParams) :
    ∀ p ∈ (st.addFunc f).ctx.fnDecls,
      p ∈ st.ctx.fnDecls ∨ p = (f.name.name, List.foldr LMonoTy.arrow f.output f.inputs.values) := by
  intro p hp
  unfold CollectState.addFunc at hp
  split at hp
  · exact Or.inl hp
  · rw [List.mem_append, List.mem_singleton] at hp
    exact hp

/-- List-fold version of the `fnDecls` correspondence. -/
theorem foldl_matStep_fnDecls_mem :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState) (p : String × LMonoTy),
      p ∈ (l.foldl (fun s f => if s.seenFns.contains f.name.name then s.addFunc f else s) st).ctx.fnDecls →
      p ∈ st.ctx.fnDecls ∨ ∃ f ∈ l, f.name.name ∈ st.seenFns ∧
        p = (f.name.name, List.foldr LMonoTy.arrow f.output f.inputs.values) := by
  intro l
  induction l with
  | nil => intro st p h; exact Or.inl h
  | cons a t ih =>
      intro st p h
      rw [List.foldl_cons] at h
      rcases ih _ p h with h1 | ⟨f, hf, hrest⟩
      · by_cases hc : (st.seenFns.contains a.name.name) = true
        · rw [if_pos hc] at h1
          rcases addFunc_fnDecls_mem st a p h1 with hh | hh
          · exact Or.inl hh
          · have haseen : a.name.name ∈ st.seenFns := by
              simp only [List.contains_eq_mem, decide_eq_true_eq] at hc; exact hc
            exact Or.inr ⟨a, List.mem_cons_self, haseen, hh⟩
        · rw [if_neg hc] at h1; exact Or.inl h1
      · have hs : f.name.name ∈ st.seenFns := by rw [← matStep_seenFns st a]; exact hrest.1
        exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hs, hrest.2⟩

/-- `materializeFuncs`-level `fnDecls` correspondence. -/
theorem materializeFuncs_fnDecls_mem (st : CollectState) (F : Lambda.Factory CoreLParams) :
    ∀ p ∈ (st.materializeFuncs F).ctx.fnDecls,
      p ∈ st.ctx.fnDecls ∨ ∃ f ∈ F.toArray, f.name.name ∈ st.seenFns ∧
        p = (f.name.name, List.foldr LMonoTy.arrow f.output f.inputs.values) := by
  intro p hp
  unfold CollectState.materializeFuncs at hp
  rw [← Array.foldl_toList] at hp
  rcases foldl_matStep_fnDecls_mem F.toArray.toList st p hp with h | ⟨f, hf, hrest⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, by simpa using hf, hrest⟩

/-- Reachable-`fnDecls` correspondence for the whole obligation. -/
theorem collectObligation_fnDecls_mem {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {karities : KnownTypeArities}
    (d : Imperative.ProofObligation Expression) :
    ∀ p ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDecls,
      ∃ f ∈ F.toArray, f.name.name ∈ (collectFuncsState uAT F tf d).seenFns ∧
        p = (f.name.name, List.foldr LMonoTy.arrow f.output f.inputs.values) := by
  intro p hp
  simp only [collectObligation] at hp
  rw [foldl_ctx_proj (·.fnDecls)
      (fun s e => by unfold collectTypes
                     exact collectTypesGo_ctx_proj uAT tf karities (·.fnDecls)
                       (fun _ _ => rfl) (fun _ _ _ => rfl) s _)] at hp
  rcases materializeFuncs_fnDecls_mem _ F p hp with h | hcorr
  · exfalso
    rw [foldl_ctx_proj (·.fnDecls) (fun s e => by rw [collectFuncs_ctx])] at h
    have hnil : ((({ ctx := { (CoreCtx.addObligationEntries {} d) with
        varDecls := unmanagedFVars d ++ (CoreCtx.addObligationEntries {} d).varDecls } } : CollectState)).ctx.fnDecls)
        = [] := obligationBaseCtx_fnDecls_nil d
    rw [hnil] at h; exact List.not_mem_nil h
  · exact hcorr

/-- One `stepCtx` extension preserves "all context types are base" (a `.varDecl`'s added monotype is base
    by its `PathEntryWF`). -/
theorem stepCtx_base {Ψ : FnCtx} {Φ0 : FVarCtx} {entry : Imperative.PathConditionEntry Expression}
    {uAT : Bool} (hpc : PathEntryWF Ψ Φ0 entry) (hΦ0 : ∀ p ∈ Φ0, tyNameRefs uAT p.2 = []) :
    ∀ p ∈ stepCtx Φ0 entry, tyNameRefs uAT p.2 = [] := by
  intro q hq
  cases entry with
  | assumption _ _ => exact hΦ0 q hq
  | varDecl name ty dv =>
    simp only [stepCtx] at hq
    split at hq
    · rename_i mty hmty
      rcases List.mem_cons.mp hq with rfl | hq'
      · cases hpc with
        | varDeclDet hmono' hbase' _ _ _ =>
          rw [hmono'] at hmty; injection hmty with h; subst h; exact tyNameRefs_of_base hbase'
        | varDeclNondet hmono' hbase' _ _ =>
          rw [hmono'] at hmty; injection hmty with h; subst h; exact tyNameRefs_of_base hbase'
      · exact hΦ0 q hq'
    · exact hΦ0 q hq
  | distinct _ _ => exact hΦ0 q hq

/-- The `stepCtx`-fold context has all-base types (under `PathEntriesWF`). -/
theorem pathEntriesWF_accum_base {Ψ : FnCtx} (uAT : Bool) :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      PathEntriesWF Ψ Φ0 es → (∀ p ∈ Φ0, tyNameRefs uAT p.2 = []) →
      ∀ p ∈ es.foldl stepCtx Φ0, tyNameRefs uAT p.2 = [] := by
  intro es
  induction es with
  | nil => intro Φ0 _ hΦ0 p hp; exact hΦ0 p hp
  | cons entry rest ih =>
    intro Φ0 hwf hΦ0
    obtain ⟨hpc, hrest⟩ := hwf.consInv
    rw [List.foldl_cons]
    exact ih (stepCtx Φ0 entry) hrest (stepCtx_base hpc hΦ0)

/-- Every expression an entry contributes to `obligationExprs` mentions no non-builtin type name. -/
theorem pathEntriesWF_exprTypeRefs_nil {Ψ : FnCtx} (uAT : Bool)
    (hΨ : ∀ p ∈ Ψ, tyNameRefs uAT p.2 = []) :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      PathEntriesWF Ψ Φ0 es → (∀ p ∈ Φ0, tyNameRefs uAT p.2 = []) →
      ∀ entry ∈ es, ∀ e ∈ oblExprStep entry, exprTypeRefs uAT e = [] := by
  intro es
  induction es with
  | nil => intro Φ0 _ _ entry hentry; simp at hentry
  | cons entry rest ih =>
    intro Φ0 hwf hΦ0 entry' hentry' e he
    obtain ⟨hpc, hrest⟩ := hwf.consInv
    rcases List.mem_cons.mp hentry' with rfl | hmem
    · cases hpc with
      | assumption ha =>
        simp only [oblExprStep, List.mem_singleton] at he; subst he
        exact hasSimpType_exprTypeRefs_nil uAT hΦ0 hΨ ha
      | varDeclDet hmono hbase hty _ _ =>
        simp only [oblExprStep, List.mem_singleton] at he; subst he
        exact hasSimpType_exprTypeRefs_nil uAT hΦ0 hΨ hty
      | varDeclNondet _ _ _ _ => simp only [oblExprStep, List.not_mem_nil] at he
      | distinct _ hex =>
        obtain ⟨τ, _, hall⟩ := hex
        simp only [oblExprStep] at he
        exact hasSimpType_exprTypeRefs_nil uAT hΦ0 hΨ (hall e he)
    · exact ih (stepCtx Φ0 entry) hrest (stepCtx_base hpc hΦ0) entry' hmem e he

/-- Every `obligationExprs` expression mentions no non-builtin type name. -/
theorem obligationExprs_exprTypeRefs_nil {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression} (hpwf : ProofObligation.WF F tf d)
    (hsimp : Factory.SimpWF F tf) :
    ∀ e ∈ obligationExprs d, exprTypeRefs uAT e = [] := by
  intro e he
  have hΨnil : ∀ p ∈ factoryFnCtx F tf, tyNameRefs uAT p.2 = [] := factoryFnCtx_annot_nil hsimp
  unfold obligationExprs at he
  rw [List.mem_append] at he
  rcases he with he | he
  · rw [List.mem_flatMap] at he
    obtain ⟨entry, hentry, hin⟩ := he
    exact pathEntriesWF_exprTypeRefs_nil uAT hΨnil d.assumptions.flatten [] hpwf.entriesWF
      (by simp) entry hentry e hin
  · simp only [List.mem_singleton] at he; subst he
    exact hasSimpType_exprTypeRefs_nil uAT
      (pathEntriesWF_accum_base uAT d.assumptions.flatten [] hpwf.entriesWF (by simp)) hΨnil hpwf.goalWF

/-- A `List.foldl` whose step fixes a specific seed on every element stays at that seed. -/
theorem foldl_fixed {α β : Type} (f : β → α → β) (init : β) :
    ∀ (l : List α), (∀ a ∈ l, f init a = init) → l.foldl f init = init := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    rw [List.foldl_cons, h x List.mem_cons_self]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- The collected context is datatype-free — DERIVED, not assumed. The verified `HasSimpType` fragment is
    base-only, so no non-builtin type name is reachable; the type walk resolves no datatype against `tf`. -/
theorem collectObligation_datatypeFree_of_WF {uAT : Bool} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf) :
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).datatypes = [] ∧
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).datatypeFuns = ∅ := by
  -- seen ⟹ nonPredefined (for the collected fnDecls/fnDefs base sigs).
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hpwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  -- `stM.ctx` datatypes/datatypeFuns are those of the raw partition (materialize doesn't touch them).
  have hdt : ((collectFuncsState uAT F tf d).materializeFuncs F).ctx.datatypes = [] := by
    rw [materializeFuncs_ctx_proj _ F (·.datatypes)
      (fun s f => by unfold CollectState.addFunc; split <;> rfl)]
    rw [foldl_ctx_proj (·.datatypes) (fun s e => by rw [collectFuncs_ctx])]
    exact obligationBaseCtx_datatypes_nil d
  have hdf : ((collectFuncsState uAT F tf d).materializeFuncs F).ctx.datatypeFuns = ∅ := by
    rw [materializeFuncs_ctx_proj _ F (·.datatypeFuns)
      (fun s f => by unfold CollectState.addFunc; split <;> rfl)]
    rw [foldl_ctx_proj (·.datatypeFuns) (fun s e => by rw [collectFuncs_ctx])]
    exact obligationBaseCtx_datatypeFuns_empty d
  -- Every signature in `stM.ctx` is base-typed, so it contributes no type-name seed.
  have hsig : ((collectFuncsState uAT F tf d).materializeFuncs F).ctx.fnSigTypeRefs uAT = [] := by
    unfold CoreCtx.fnSigTypeRefs
    rw [List.append_eq_nil_iff]
    refine ⟨List.flatMap_eq_nil_iff.mpr ?_, List.flatMap_eq_nil_iff.mpr ?_⟩
    · intro p hp
      rcases materializeFuncs_fnDecls_mem _ F p hp with h | ⟨f, hf, hfseen, hpe⟩
      · rw [foldl_ctx_proj (·.fnDecls) (fun s e => by rw [collectFuncs_ctx])] at h
        rw [obligationBaseCtx_fnDecls_nil d] at h; exact absurd h (List.not_mem_nil)
      · subst hpe
        have hsimpSig := hsimp.fnsSigSimp f (f_nonPred f hf hfseen)
        show tyNameRefs uAT (List.foldr LMonoTy.arrow f.output f.inputs.values) = []
        rw [← mkArrow'_eq_foldr]
        exact tyNameRefs_mkArrow'_base uAT f.inputs.values f.output hsimpSig.fnArgsBase hsimpSig.fnRetBase
    · intro d' hd'
      rcases materializeFuncs_fnDefs_mem _ F d' hd' with h | ⟨f, hf, hfseen, hrec, body, hbody, hname, hargs, hret, hbdy⟩
      · rw [foldl_ctx_proj (·.fnDefs) (fun s e => by rw [collectFuncs_ctx])] at h
        rw [obligationBaseCtx_fnDefs_nil d] at h; exact absurd h (List.not_mem_nil)
      · have hsimpSig := hsimp.fnsSigSimp f (f_nonPred f hf hfseen)
        rw [List.append_eq_nil_iff]
        refine ⟨List.flatMap_eq_nil_iff.mpr ?_, ?_⟩
        · intro a ha; rw [hargs] at ha; exact tyNameRefs_of_base (hsimpSig.fnArgsBase a ha)
        · rw [hret]; exact tyNameRefs_of_base hsimpSig.fnRetBase
  -- The `collectTypes` fold is fixed at `stM` (each expression's type worklist is empty).
  rw [collectObligation_eq_collectTypesFold]
  have hfold : (obligationExprs d).foldl (collectTypes uAT tf karities)
      ((collectFuncsState uAT F tf d).materializeFuncs F)
      = (collectFuncsState uAT F tf d).materializeFuncs F := by
    apply foldl_fixed
    intro e he
    unfold collectTypes
    rw [obligationExprs_exprTypeRefs_nil hpwf hsimp e he, hsig, List.nil_append]
    simp only [collectTypesGo]
  rw [hfold]
  -- `datatypes` is the block-regroup of the reached type names; the function walk adds none, so the
  -- reached-set is empty and the regroup collapses to `[]`.
  have hseen : ((collectFuncsState uAT F tf d).materializeFuncs F).seenTypes = [] := by
    rw [materializeFuncs_seenTypes]
    unfold collectFuncsState
    rw [foldl_seenTypes_fixed (fun s e => collectFuncs_seenTypes uAT F tf s e)]
  refine ⟨?_, hdf⟩
  rw [hseen]; simp [datatypeBlocksLD]

mutual
/-- Restriction of `HasSimpType` to a smaller function context `Ψ'` containing every non-predefined
    `.op`-head pair used in `e` (predefined heads type via `AppSpine.op`, which ignores `Ψ`). -/
theorem HasSimpType.restrict_fn {Φ : FVarCtx} {Ψ Ψ' : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (hused : ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false → p ∈ Ψ')
    (h : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.HasSimpType Φ Ψ' Δ e τ := by
  match h with
  | .const c hbase => exact .const c hbase
  | .bvar i τ hlook hbase => exact .bvar i τ hlook hbase
  | .app fn arg rty hspine => exact .app fn arg rty (AppSpine.restrict_fn hused hspine)
  | .fvarNullary f τ rty hspine =>
      exact .fvarNullary f τ rty (AppSpine.restrict_fn (by intro p hp; simp [exprFnOps] at hp) hspine)
  | .ite c t τ e_ hc ht hee =>
      refine .ite c t τ e_ (HasSimpType.restrict_fn ?_ hc) (HasSimpType.restrict_fn ?_ ht)
        (HasSimpType.restrict_fn ?_ hee)
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inl (Or.inl hp)) hnpre
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inl (Or.inr hp)) hnpre
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inr hp) hnpre
  | .eq e1 e2 τ hbase he1 he2 =>
      refine .eq e1 e2 τ hbase (HasSimpType.restrict_fn ?_ he1) (HasSimpType.restrict_fn ?_ he2)
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inl hp) hnpre
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inr hp) hnpre
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
      refine .quant qty qbody qk qname qtr qτtr hbase (HasSimpType.restrict_fn ?_ htr)
        (HasSimpType.restrict_fn ?_ hbody)
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inl hp) hnpre
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inr hp) hnpre
/-- Restriction of `AppSpine`, mutual with `HasSimpType.restrict_fn`. -/
theorem AppSpine.restrict_fn {Φ : FVarCtx} {Ψ Ψ' : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hused : ∀ p ∈ exprFnOps e, isPredefinedOp p.1 = false → p ∈ Ψ')
    (h : LExpr.AppSpine Φ Ψ Δ e acc rty) : LExpr.AppSpine Φ Ψ' Δ e acc rty := by
  match h with
  | .app fn arg aty acc rty harg hrest =>
      refine .app fn arg aty acc rty (HasSimpType.restrict_fn ?_ harg) (AppSpine.restrict_fn ?_ hrest)
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inr hp) hnpre
      · intro p hp hnpre; exact hused p (by simp only [exprFnOps, List.mem_append]; exact Or.inl hp) hnpre
  | .fvar f τ acc rty hmem hcol hbase => exact .fvar f τ acc rty hmem hcol hbase
  | .op o oty acc rty hop hcol => exact .op o oty acc rty hop hcol
  | .fnOp o oty acc rty hmem hnpre hcol hbase =>
      exact .fnOp o oty acc rty (hused (o.name, oty) (by simp [exprFnOps]) hnpre) hnpre hcol hbase
termination_by structural h
end

/-- The collected function context is a subset of the whole-factory user-function context: every collected
    `fnDecl`/`fnDef` is a materialized (hence seen ⟹ `nonPredefined`) factory function. -/
theorem collectObligation_toΨ_subset {uAT : Bool} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf) :
    (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ ⊆ factoryFnCtx F tf := by
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hpwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  intro x hx
  unfold CoreCtx.toΨ at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨f, hf, hfseen, heq⟩ := collectObligation_fnDecls_mem d x hx
    subst heq
    refine List.mem_map.mpr ⟨f, f_nonPred f hf hfseen, ?_⟩
    rw [mkArrow'_eq_foldr]
  · rw [List.mem_map] at hx
    obtain ⟨d', hd', hxeq⟩ := hx
    obtain ⟨f, hf, hfseen, hrec, body, hbody, hname, hargs, hret, hbdy⟩ :=
      collectObligation_fnDefs_mem d d' hd'
    refine List.mem_map.mpr ⟨f, f_nonPred f hf hfseen, ?_⟩
    rw [← hxeq, hname, hret, hargs]

/-- `factoryFnCtx F tf` has functional names: an entry is determined by its name (factory names are nodup). -/
theorem factoryFnCtx_functional {F : Lambda.Factory CoreLParams} {a b : String × LMonoTy}
    (ha : a ∈ factoryFnCtx F tf) (hb : b ∈ factoryFnCtx F tf) (hname : a.1 = b.1) : a = b := by
  obtain ⟨fa, hfa, rfl⟩ := List.mem_map.mp ha
  obtain ⟨fb, hfb, rfl⟩ := List.mem_map.mp hb
  have hfaA : fa ∈ F.toArray := Array.mem_toList_iff.mp (List.mem_filter.mp hfa).1
  have hfbA : fb ∈ F.toArray := Array.mem_toList_iff.mp (List.mem_filter.mp hfb).1
  simp only at hname
  obtain ⟨hsa, hea⟩ := Factory.mem_name_eq_getElem hfaA rfl
  obtain ⟨hsb, heb⟩ := Factory.mem_name_eq_getElem hfbA hname.symm
  have : fa = fb := by rw [← hea, ← heb]
  rw [this]

mutual
/-- Weakening of `HasSimpType` in the free-var context: enlarging `Φ` (as a membership set) preserves
    typing (the only positive use of `Φ` is `AppSpine.fvar`'s `(f.name,τ) ∈ Φ`). -/
theorem HasSimpType.weaken_fvar {Φ Φ' : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy} (hsub : Φ ⊆ Φ')
    (h : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.HasSimpType Φ' Ψ Δ e τ := by
  match h with
  | .const c hbase => exact .const c hbase
  | .bvar i τ hlook hbase => exact .bvar i τ hlook hbase
  | .app fn arg rty hspine => exact .app fn arg rty (AppSpine.weaken_fvar hsub hspine)
  | .fvarNullary f τ rty hspine => exact .fvarNullary f τ rty (AppSpine.weaken_fvar hsub hspine)
  | .ite c t τ e_ hc ht hee =>
      exact .ite c t τ e_ (HasSimpType.weaken_fvar hsub hc) (HasSimpType.weaken_fvar hsub ht)
        (HasSimpType.weaken_fvar hsub hee)
  | .eq e1 e2 τ hbase he1 he2 =>
      exact .eq e1 e2 τ hbase (HasSimpType.weaken_fvar hsub he1) (HasSimpType.weaken_fvar hsub he2)
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody =>
      exact .quant qty qbody qk qname qtr qτtr hbase (HasSimpType.weaken_fvar hsub htr)
        (HasSimpType.weaken_fvar hsub hbody)
theorem AppSpine.weaken_fvar {Φ Φ' : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy} (hsub : Φ ⊆ Φ')
    (h : LExpr.AppSpine Φ Ψ Δ e acc rty) : LExpr.AppSpine Φ' Ψ Δ e acc rty := by
  match h with
  | .app fn arg aty acc rty harg hrest =>
      exact .app fn arg aty acc rty (HasSimpType.weaken_fvar hsub harg) (AppSpine.weaken_fvar hsub hrest)
  | .fvar f τ acc rty hmem hcol hbase => exact .fvar f τ acc rty (hsub hmem) hcol hbase
  | .op o oty acc rty hop hcol => exact .op o oty acc rty hop hcol
  | .fnOp o oty acc rty hmem hnpre hcol hbase => exact .fnOp o oty acc rty hmem hnpre hcol hbase
termination_by structural h
end

/-- **Name ⟹ pair** in the collected `toΨ`: a typed non-predefined op-head (so `∈ factoryFnCtx`) whose
    NAME is reachable (`∈ toΨ` names) has its whole PAIR in `toΨ` — factory names are functional. -/
theorem exprFnOps_pair_mem_of_name {F : Lambda.Factory CoreLParams} {toΨ : FnCtx}
    (hsub : toΨ ⊆ factoryFnCtx F tf) {p : String × LMonoTy}
    (hpfac : p ∈ factoryFnCtx F tf) (hname : p.1 ∈ toΨ.map Prod.fst) : p ∈ toΨ := by
  obtain ⟨p', hp'mem, hp'name⟩ := List.mem_map.mp hname
  have hpp' : p = p' := factoryFnCtx_functional hpfac (hsub hp'mem) hp'name.symm
  rw [hpp']; exact hp'mem

/-- The `stepCtx`-fold context is contained (as a membership set) in the partition's `varDecls ++
    varDefs`-names — the same variables, split by det/nondet across `varDecls`/`varDefs`. -/
theorem foldl_stepCtx_sub_oblStep :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (c : CoreCtx),
      (∀ p ∈ Φ0, p ∈ c.varDecls ++ c.varDefs.map (fun v => (v.name, v.ty))) →
      ∀ p ∈ es.foldl stepCtx Φ0,
        p ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls ++
        (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs.map
            (fun v => (v.name, v.ty)) := by
  intro es
  induction es with
  | nil => intro Φ0 c hinv p hp; exact hinv p hp
  | cons entry rest ih =>
    intro Φ0 c hinv p hp
    simp only [List.foldl_cons] at hp ⊢
    cases entry with
    | assumption l e =>
      simp only [stepCtx] at hp
      exact ih Φ0 { c with assumptions := c.assumptions ++ [e] } hinv p hp
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [stepCtx, hm] at hp ⊢
          exact ih Φ0 c hinv p hp
        | some mty =>
          simp only [stepCtx, hm] at hp ⊢
          refine ih ((name.name, mty) :: Φ0)
            { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] } ?_ p hp
          intro q hq
          simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
            List.mem_append, List.mem_singleton]
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact Or.inr rfl
          · exact Or.inl (List.mem_append.mp (hinv q hq'))
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [stepCtx, hm] at hp ⊢
          exact ih Φ0 c hinv p hp
        | some mty =>
          simp only [stepCtx, hm] at hp ⊢
          refine ih ((name.name, mty) :: Φ0)
            { c with varDecls := c.varDecls ++ [(name.name, mty)] } ?_ p hp
          intro q hq
          simp only [List.mem_append, List.mem_singleton]
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact Or.inl (Or.inr rfl)
          · rcases List.mem_append.mp (hinv q hq') with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
    | distinct l es' =>
      simp only [stepCtx] at hp
      exact ih Φ0 { c with distincts := c.distincts ++ [es'] } hinv p hp

/-- Every free-var pair the obligation types against (`accumFVarCtx`) is in the collected `toΦ`. -/
theorem accumFVarCtx_sub_obligationBaseCtx_toΦ (d : Imperative.ProofObligation Expression) :
    ∀ p ∈ accumFVarCtx d.assumptions.flatten,
      p ∈ (obligationBaseCtx d).varDecls ++
        (obligationBaseCtx d).varDefs.map (fun v => (v.name, v.ty)) := by
  intro p hp
  unfold accumFVarCtx at hp
  unfold obligationBaseCtx CoreCtx.addObligationEntries
  exact foldl_stepCtx_sub_oblStep d.assumptions.flatten [] {} (by simp) p hp

/-- The `FnDef`→signature map used by `CoreCtx.toΨ`. -/
private abbrev fnDefSig (d : FnDef) : String × LMonoTy := (d.name, LMonoTy.mkArrow' d.retTy d.argTys)

/-- Append one well-typed `fnDef` at the END of an order-aware `FnDefsWF` chain (its body typed against
    the full accumulated prefix `Ψ0 ++ fnDefs`). -/
theorem FnDefsWF_snoc :
    ∀ (Ψ0 : FnCtx) (fnDefs : List FnDef) (d : FnDef),
      FnDefsWF Ψ0 fnDefs →
      LExpr.HasSimpType [] (Ψ0 ++ fnDefs.map fnDefSig) d.argTys d.body d.retTy →
      (∀ t ∈ d.argTys, LExpr.MonoTyIsBase t) →
      (d.params.map Prod.fst).Nodup →
      (∀ p ∈ d.params, p.1 ∉ (Ψ0 ++ fnDefs.map fnDefSig).map Prod.fst) →
      FnDefsWF Ψ0 (fnDefs ++ [d]) := by
  intro Ψ0 fnDefs
  induction fnDefs generalizing Ψ0 with
  | nil =>
    intro d h hbody hargs hnodup hfresh
    simp only [List.map_nil, List.append_nil] at hbody hfresh
    exact FnDefsWF.cons hbody hargs hnodup hfresh FnDefsWF.nil
  | cons d' rest ih =>
    intro d h hbody hargs hnodup hfresh
    cases h with
    | @cons _ _ _ hty' hargs' hnodup' hfresh' hrestWF =>
      rw [List.cons_append]
      refine FnDefsWF.cons hty' hargs' hnodup' hfresh' (ih (Ψ0 ++ [fnDefSig d']) d hrestWF ?_ hargs hnodup ?_)
      · simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using hbody
      · intro p hp
        have := hfresh p hp
        simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.map_append] using this

/-- Folding the materialize step over a list equals folding it over the `p`-filtered list, when every
    dropped element is a no-op (its name is unseen). Uses that the step preserves `seenFns`. -/
theorem foldl_matStep_filter (p : LFunc CoreLParams → Bool) :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState),
      (∀ g ∈ l, p g = false → g.name.name ∉ st.seenFns) →
      (l.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) st).ctx
      = ((l.filter p).foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) st).ctx := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons g rest ih =>
    intro st hskip
    rw [List.foldl_cons, List.filter_cons]
    by_cases hp : p g
    · rw [hp, if_pos rfl, List.foldl_cons]
      rw [ih (if st.seenFns.contains g.name.name then st.addFunc g else st)]
      intro g' hg' hpg'
      rw [matStep_seenFns st g]
      exact hskip g' (List.mem_cons_of_mem _ hg') hpg'
    · have hgunseen : g.name.name ∉ st.seenFns :=
        hskip g List.mem_cons_self (by simpa using hp)
      have hstep : (if st.seenFns.contains g.name.name then st.addFunc g else st) = st := by
        rw [if_neg (by simp only [List.contains_eq_mem, decide_eq_true_eq]; exact hgunseen)]
      simp only [hp, Bool.false_eq_true, if_false]
      rw [hstep] at *
      rw [ih st (fun g' hg' hpg' => hskip g' (List.mem_cons_of_mem _ hg') hpg')]

/-- **The order-aware `FnDefsWF` construction** (materialize-fold over `nonPredefined`, aligned with
    `FactoryFnsWF`'s threading). Builds `FnDefsWF finalDecls (fold).fnDefs` incrementally: each seen
    non-recursive-with-body function is appended (`FnDefsWF_snoc`), its body retyped from the threaded
    `Ψ0` to `finalDecls ++ (fnDefs so far)` (the body's op-heads are in `Ψ0` and — being reachable/seen —
    already materialized, per the `hI2` invariant). `finalDecls` is fixed, so declaration steps are no-ops
    for the `fnDefs` chain. -/
theorem factory_FnDefsWF_aux {uAT : Bool} {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (hsimp : Factory.SimpWF F tf)
    (SEEN : List String)
    (finalDecls : FnCtx) (hfinalDeclsSub : ∀ p ∈ finalDecls, p ∈ factoryFnCtx F tf)
    (hclosed : ∀ g ∈ F.toArray, g.name.name ∈ SEEN → ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome →
      Core.NameMangling.demangledBaseName h ∉ datatypeOpNames tf → h ∈ SEEN)
    (hnpNr : ∀ g ∈ Factory.nonPredefined F tf, g.name.name ∈ SEEN → (g.isRecursive = true ∨ g.body = none) →
      (g.name.name, LMonoTy.mkArrow' g.output g.inputs.values) ∈ finalDecls) :
    ∀ (Ψ0 : FnCtx) (fns : List (LFunc CoreLParams)) (acc : CollectState),
      FactoryFnsWF Ψ0 fns → (∀ g ∈ fns, g ∈ Factory.nonPredefined F tf) → acc.seenFns = SEEN →
      (∀ p ∈ Ψ0, p ∈ factoryFnCtx F tf) →
      FnDefsWF finalDecls acc.ctx.fnDefs →
      (∀ p ∈ acc.ctx.fnDefs.map fnDefSig, p ∈ factoryFnCtx F tf) →
      (∀ nm ty, (nm, ty) ∈ Ψ0 → nm ∈ SEEN → (nm, ty) ∈ finalDecls ++ acc.ctx.fnDefs.map fnDefSig) →
      FnDefsWF finalDecls
        ((fns.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) acc).ctx.fnDefs) := by
  intro Ψ0 fns acc hfac
  induction hfac generalizing acc with
  | nil => intro _ _ _ hwf _ _; exact hwf
  | @cons Ψ f rest hbody hrestFac ih =>
    intro hsub hseen hΨsub hwf haccSub hI2
    have hfnp : f ∈ Factory.nonPredefined F tf := hsub f List.mem_cons_self
    have hfF : f ∈ F.toArray := Array.mem_toList_iff.mp (List.mem_filter.mp hfnp).1
    have hfsigfac : (f.name.name, LMonoTy.mkArrow' f.output f.inputs.values) ∈ factoryFnCtx F tf :=
      List.mem_map.mpr ⟨f, hfnp, rfl⟩
    have hΨsub' : ∀ p ∈ Ψ ++ [(f.name.name, LMonoTy.mkArrow' f.output f.inputs.values)],
        p ∈ factoryFnCtx F tf := by
      intro p hp; rw [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hΨsub p hp
      · exact hfsigfac
    have hrestSub : ∀ g ∈ rest, g ∈ Factory.nonPredefined F tf := fun g hg => hsub g (List.mem_cons_of_mem _ hg)
    rw [List.foldl_cons]
    by_cases hfseen : acc.seenFns.contains f.name.name
    · -- f is seen
      have hfseenMem : f.name.name ∈ SEEN := by rw [← hseen]; simpa using hfseen
      rw [if_pos hfseen]
      by_cases hnr : f.isRecursive = false ∧ f.body ≠ none
      · -- non-recursive with a body: a `define-fun` is appended
        obtain ⟨hrecF, hbNe⟩ := hnr
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hbNe
        have hArgTys : (((f.inputs.keys.map (·.name)).zip f.inputs.values).map (·.2)) = f.inputs.values := by
          apply List.map_snd_zip
          simp [List.length_map, ListMap.keys.length, ListMap.values_eq_map_snd]
        have haddDefs : (acc.addFunc f).ctx.fnDefs = acc.ctx.fnDefs ++
            [(⟨f.name.name, (f.inputs.keys.map (·.name)).zip f.inputs.values, f.output,
               LExpr.substFvarsLifting b (funcBvarSubst f)⟩ : FnDef)] := by
          unfold CollectState.addFunc; simp only [hrecF, hb]
        have hfdefSig : fnDefSig (⟨f.name.name, (f.inputs.keys.map (·.name)).zip f.inputs.values, f.output,
            LExpr.substFvarsLifting b (funcBvarSubst f)⟩ : FnDef)
            = (f.name.name, LMonoTy.mkArrow' f.output f.inputs.values) := by
          simp only [fnDefSig, FnDef.argTys]; rw [hArgTys]
        -- op-heads of the body are already materialized
        have hbodyTyped : LExpr.HasSimpType [] (finalDecls ++ acc.ctx.fnDefs.map fnDefSig)
            f.inputs.values (LExpr.substFvarsLifting b (funcBvarSubst f)) f.output := by
          refine HasSimpType.restrict_fn ?_ (hbody b hrecF hb)
          intro p hp hnpre
          have hpΨ : p ∈ Ψ := hasSimpType_fnOps_mem (hbody b hrecF hb) p hp hnpre
          have hpfac : p ∈ factoryFnCtx F tf := hΨsub p hpΨ
          have hp1mem : p.1 ∈ (factoryFnCtx F tf).map Prod.fst := List.mem_map.mpr ⟨p, hpfac, rfl⟩
          obtain ⟨g', hg', hg'name⟩ := factoryFnCtx_name_mem hp1mem
          have hnone := corePredefinedOp_none_of_notPredefined (uAT := uAT) hnpre
          have hp1ref : p.1 ∈ exprFnRefs uAT (LExpr.substFvarsLifting b (funcBvarSubst f)) :=
            exprFnOps_name_mem_exprFnRefs _ p hp hnone
          rw [exprFnRefs_substFvarsLifting_funcBvarSubst] at hp1ref
          have hp1edge : p.1 ∈ funcFnRefs uAT f := by
            unfold funcFnRefs; rw [List.mem_append]; left
            simp only [hrecF, hb, Bool.false_eq_true, if_false, Option.map_some, Option.getD_some]
            exact hp1ref
          have hp1seen : p.1 ∈ SEEN := hclosed f hfF hfseenMem p.1 hp1edge
            (factory_getElem?_isSome_of_mem hg' hg'name) (factoryFnCtx_notDatatypeOp hp1mem)
          exact hI2 p.1 p.2 hpΨ hp1seen
        refine ih (acc.addFunc f) hrestSub (by rw [addFunc_seenFns]; exact hseen) hΨsub' ?_ ?_ ?_
        · -- FnDefsWF finalDecls (acc.addFunc f).fnDefs
          rw [haddDefs]
          refine FnDefsWF_snoc finalDecls acc.ctx.fnDefs _ hwf ?_ ?_ ?_ ?_
          · show LExpr.HasSimpType [] (finalDecls ++ acc.ctx.fnDefs.map fnDefSig)
              (((f.inputs.keys.map (·.name)).zip f.inputs.values).map (·.2)) _ f.output
            rw [hArgTys]; exact hbodyTyped
          · show ∀ t ∈ (((f.inputs.keys.map (·.name)).zip f.inputs.values).map (·.2)), LExpr.MonoTyIsBase t
            rw [hArgTys]; exact (hsimp.fnsSigSimp f hfnp).fnArgsBase
          · show (((f.inputs.keys.map (·.name)).zip f.inputs.values).map Prod.fst).Nodup
            rw [List.map_fst_zip (by simp [List.length_map, ListMap.keys.length, ListMap.values_eq_map_snd])]
            exact (hsimp.fnsSigSimp f hfnp).fnParamsWF
          · -- params fresh vs the accumulated function names
            intro p hp hmem
            have hp1 : p.1 ∈ (f.inputs.keys.map (·.name)) := (List.of_mem_zip hp).1
            obtain ⟨k, hk, hkname⟩ := List.mem_map.mp hp1
            have hfresh := (hsimp.fnsSigSimp f hfnp).fnParamsFresh k hk
            rw [hkname] at hfresh
            apply hfresh
            obtain ⟨q, hq, hqname⟩ := List.mem_map.mp hmem
            rw [List.mem_append] at hq
            refine List.mem_map.mpr ⟨q, ?_, hqname⟩
            rcases hq with hq | hq
            · exact hfinalDeclsSub q hq
            · exact haccSub q hq
        · -- haccSub'
          rw [haddDefs]
          intro p hp
          rw [List.map_append, List.mem_append] at hp
          rcases hp with hp | hp
          · exact haccSub p hp
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hp
            subst hp
            rw [hfdefSig]; exact hfsigfac
        · -- hI2'
          rw [haddDefs]
          intro nm ty hnt hnmseen
          rw [List.mem_append, List.mem_singleton] at hnt
          rw [List.map_append, ← List.append_assoc]
          rcases hnt with hnt | heq
          · exact List.mem_append_left _ (hI2 nm ty hnt hnmseen)
          · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine List.mem_append_right _ ?_
            simp only [List.map_cons, List.map_nil, List.mem_singleton]
            exact hfdefSig.symm
      · -- recursive or bodyless: a `declare-fun` is appended; `fnDefs` unchanged
        have hrecOrBody : f.isRecursive = true ∨ f.body = none := by
          rcases Classical.em (f.body = none) with hb | hb
          · exact Or.inr hb
          · exact Or.inl (by
              cases hc : f.isRecursive with
              | false => exact absurd ⟨hc, hb⟩ hnr
              | true => rfl)
        have haddDefs : (acc.addFunc f).ctx.fnDefs = acc.ctx.fnDefs := by
          unfold CollectState.addFunc
          cases hr : f.isRecursive <;> cases hbd : f.body <;> simp only [] <;> try rfl
          exact absurd ⟨hr, by rw [hbd]; exact Option.some_ne_none _⟩ hnr
        refine ih (acc.addFunc f) hrestSub (by rw [addFunc_seenFns]; exact hseen) hΨsub'
          (by rw [haddDefs]; exact hwf) (by rw [haddDefs]; exact haccSub) ?_
        rw [haddDefs]
        intro nm ty hnt hnmseen
        rw [List.mem_append, List.mem_singleton] at hnt
        rcases hnt with hnt | heq
        · exact hI2 nm ty hnt hnmseen
        · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
          exact List.mem_append_left _ (hnpNr f hfnp hfseenMem hrecOrBody)
    · -- f unseen: no change
      have hfunseen : f.name.name ∉ SEEN := by rw [← hseen]; simpa using hfseen
      rw [if_neg hfseen]
      refine ih acc hrestSub hseen hΨsub' hwf haccSub ?_
      intro nm ty hnt hnmseen
      rw [List.mem_append, List.mem_singleton] at hnt
      rcases hnt with hnt | heq
      · exact hI2 nm ty hnt hnmseen
      · rw [Prod.mk.injEq] at heq; obtain ⟨rfl, _⟩ := heq
        exact absurd hnmseen hfunseen

/-- Materialize's fold over `F.toArray` equals the fold over `nonPredefined F tf` on the resolved `ctx`
    (predefined functions are never seen, so they are no-ops). -/
theorem materializeFuncs_ctx_eq {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    (st : CollectState) (F : Lambda.Factory CoreLParams)
    (hskip : ∀ g ∈ F.toArray,
      (isPredefinedOp g.name.name = true ∨
        Core.NameMangling.demangledBaseName g.name.name ∈ datatypeOpNames tf) →
      g.name.name ∉ st.seenFns) :
    (st.materializeFuncs F).ctx
    = ((Factory.nonPredefined F tf).foldl
        (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) st).ctx := by
  unfold CollectState.materializeFuncs
  rw [← Array.foldl_toList]
  exact foldl_matStep_filter
    (fun g => !isPredefinedOp g.name.name &&
      !(Core.NameMangling.demangledBaseName g.name.name ∈ datatypeOpNames tf))
    F.toArray.toList st
    (fun g hg hpf => hskip g (Array.mem_toList_iff.mp hg) (by
      rcases Bool.and_eq_false_iff.mp hpf with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)))

/-- `addFunc` on a recursive/bodyless function adds its declared signature to `fnDecls`. -/
theorem addFunc_mem_fnDecls (acc : CollectState) (g : LFunc CoreLParams)
    (hkind : g.isRecursive = true ∨ g.body = none) :
    (g.name.name, List.foldr LMonoTy.arrow g.output g.inputs.values) ∈ (acc.addFunc g).ctx.fnDecls := by
  unfold CollectState.addFunc
  rcases hkind with hr | hb
  · cases hbd : g.body <;> simp only [hr] <;> simp [List.mem_append]
  · cases hrec : g.isRecursive <;> simp only [hb] <;> simp [List.mem_append]

/-- The materialize fold only grows `fnDecls`. -/
theorem matStep_fold_fnDecls_mono :
    ∀ (l : List (LFunc CoreLParams)) (acc : CollectState) {p : String × LMonoTy},
      p ∈ acc.ctx.fnDecls →
      p ∈ (l.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) acc).ctx.fnDecls := by
  intro l
  induction l with
  | nil => intro acc p h; exact h
  | cons g rest ih =>
    intro acc p h
    rw [List.foldl_cons]
    apply ih
    by_cases hc : acc.seenFns.contains g.name.name
    · rw [if_pos hc]
      unfold CollectState.addFunc
      split
      · exact h
      · rw [List.mem_append]; exact Or.inl h
    · rw [if_neg hc]; exact h

/-- **Forward `fnDecls` membership**: a seen recursive/bodyless function's declared signature is in the
    materialize fold's `fnDecls`. -/
theorem matStep_mem_fnDecls :
    ∀ (l : List (LFunc CoreLParams)) (acc : CollectState) (g : LFunc CoreLParams),
      g ∈ l → g.name.name ∈ acc.seenFns → (g.isRecursive = true ∨ g.body = none) →
      (g.name.name, List.foldr LMonoTy.arrow g.output g.inputs.values)
        ∈ (l.foldl (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s) acc).ctx.fnDecls := by
  intro l
  induction l with
  | nil => intro acc g hg _ _; simp at hg
  | cons x rest ih =>
    intro acc g hg hseen hkind
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hg with rfl | hg'
    · have hc : acc.seenFns.contains g.name.name := by
        simp only [List.contains_eq_mem, decide_eq_true_eq]; exact hseen
      rw [if_pos hc]
      exact matStep_fold_fnDecls_mono rest (acc.addFunc g) (addFunc_mem_fnDecls acc g hkind)
    · have hseen' : g.name.name ∈ (if acc.seenFns.contains x.name.name then acc.addFunc x else acc).seenFns := by
        rw [matStep_seenFns acc x]; exact hseen
      exact ih _ g hg' hseen' hkind

/-- **The collected `fnDefs` are order-aware well-formed** — the payoff of `factory_FnDefsWF_aux`, wired to
    the actual collected context via the materialize=`nonPredefined`-fold equality. -/
theorem collectObligation_fnDefsWF {uAT : Bool} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {F : Lambda.Factory CoreLParams}
    {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf) :
    FnDefsWF (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDecls
      (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDefs := by
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hpwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  have hclosed : ∀ g ∈ F.toArray, g.name.name ∈ (collectFuncsState uAT F tf d).seenFns →
      ∀ h ∈ funcFnRefs uAT g, (F[h]?).isSome →
        Core.NameMangling.demangledBaseName h ∉ datatypeOpNames tf →
        h ∈ (collectFuncsState uAT F tf d).seenFns :=
    foldl_collectFuncs_closed (obligationExprs d) _ (fun g _ hg => absurd hg (by simp))
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  have hskip : ∀ g ∈ F.toArray,
      (isPredefinedOp g.name.name = true ∨
        Core.NameMangling.demangledBaseName g.name.name ∈ datatypeOpNames tf) →
      g.name.name ∉ (collectFuncsState uAT F tf d).seenFns := by
    intro g _ hp hc
    rcases hp with hp | hp
    · have := hseenNP g.name.name hc; rw [hp] at this; exact absurd this (by simp)
    · exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
        (fun nm h => absurd h (by simp)) g.name.name hc hp
  have hstFdefs : (collectFuncsState uAT F tf d).ctx.fnDefs = [] := by
    rw [foldl_ctx_proj (·.fnDefs) (fun s e => by rw [collectFuncs_ctx])]
    exact obligationBaseCtx_fnDefs_nil d
  have hmat : ((collectFuncsState uAT F tf d).materializeFuncs F).ctx
      = ((Factory.nonPredefined F tf).foldl
          (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
          (collectFuncsState uAT F tf d)).ctx :=
    materializeFuncs_ctx_eq _ F hskip
  -- the collected fnDecls/fnDefs equal the nonPredefined-fold's
  have hColDecls : (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDecls
      = ((Factory.nonPredefined F tf).foldl
          (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
          (collectFuncsState uAT F tf d)).ctx.fnDecls := by
    rw [collectObligation_eq_collectTypesFold, foldl_ctx_proj (·.fnDecls)
      (fun s e => by unfold collectTypes
                     exact collectTypesGo_ctx_proj uAT tf karities (·.fnDecls)
                       (fun _ _ => rfl) (fun _ _ _ => rfl) s _), hmat]
  have hColDefs : (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).fnDefs
      = ((Factory.nonPredefined F tf).foldl
          (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
          (collectFuncsState uAT F tf d)).ctx.fnDefs := by
    rw [collectObligation_eq_collectTypesFold, foldl_ctx_proj (·.fnDefs)
      (fun s e => by unfold collectTypes
                     exact collectTypesGo_ctx_proj uAT tf karities (·.fnDefs)
                       (fun _ _ => rfl) (fun _ _ _ => rfl) s _), hmat]
  rw [hColDecls, hColDefs]
  refine factory_FnDefsWF_aux hsimp (collectFuncsState uAT F tf d).seenFns
    (((Factory.nonPredefined F tf).foldl
        (fun s g => if s.seenFns.contains g.name.name then s.addFunc g else s)
        (collectFuncsState uAT F tf d)).ctx.fnDecls) ?_ hclosed ?_
    [] (Factory.nonPredefined F tf) (collectFuncsState uAT F tf d) hsimp.fnsWF (fun g hg => hg) rfl
    (by simp) (by rw [hstFdefs]; exact FnDefsWF.nil) (by rw [hstFdefs]; simp) (by simp)
  · -- hfinalDeclsSub : finalDecls ⊆ factoryFnCtx
    intro p hp
    rw [← hColDecls] at hp
    obtain ⟨f, hf, hfseen, hpe⟩ := collectObligation_fnDecls_mem d p hp
    subst hpe
    rw [← mkArrow'_eq_foldr]
    exact List.mem_map.mpr ⟨f, f_nonPred f hf hfseen, rfl⟩
  · -- hnpNr
    intro g hg hgseen hkind
    rw [mkArrow'_eq_foldr]
    exact matStep_mem_fnDecls (Factory.nonPredefined F tf) (collectFuncsState uAT F tf d) g hg hgseen hkind

/-- `stepCtx` only extends the free-var context. -/
theorem stepCtx_super (Φ0 : FVarCtx) (entry : Imperative.PathConditionEntry Expression) :
    ∀ p ∈ Φ0, p ∈ stepCtx Φ0 entry := by
  intro p hp
  cases entry with
  | assumption _ _ => exact hp
  | varDecl name ty dv =>
    simp only [stepCtx]
    split
    · exact List.mem_cons_of_mem _ hp
    · exact hp
  | distinct _ _ => exact hp

/-- The `stepCtx`-fold only extends the free-var context. -/
theorem stepCtx_foldl_mono :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      ∀ p ∈ Φ0, p ∈ es.foldl stepCtx Φ0 := by
  intro es
  induction es with
  | nil => intro Φ0 p hp; exact hp
  | cons entry rest ih =>
    intro Φ0 p hp
    rw [List.foldl_cons]
    exact ih (stepCtx Φ0 entry) p (stepCtx_super Φ0 entry p hp)

/-- A monomorphic `.varDecl` contributes its `(name, mty)` to the `stepCtx`-fold context. -/
theorem mem_accumFVarCtx :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx)
      (name : Expression.Ident) (ty : Expression.Ty) (dv) (mty : LMonoTy),
      Imperative.PathConditionEntry.varDecl name ty dv ∈ es → ty.toMonoType? = some mty →
      (name.name, mty) ∈ es.foldl stepCtx Φ0 := by
  intro es
  induction es with
  | nil => intro Φ0 name ty dv mty hmem _; simp at hmem
  | cons entry rest ih =>
    intro Φ0 name ty dv mty hmem hmono
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have : (name.name, mty) ∈ stepCtx Φ0 (.varDecl name ty dv) := by
        simp only [stepCtx, hmono]; exact List.mem_cons_self
      exact stepCtx_foldl_mono rest (stepCtx Φ0 (.varDecl name ty dv)) _ this
    · exact ih (stepCtx Φ0 entry) name ty dv mty hmem' hmono

/-- **Accumulator-context typing** for entry-contributed expressions: each assumption/det-var body/distinct
    member is typed against the FULL accumulated free-var context `Φfull` (⊇ the entry's prefix). -/
theorem pathEntriesWF_flatMap_typed_accum {Ψ : FnCtx} (Φfull : FVarCtx) :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx),
      PathEntriesWF Ψ Φ0 es → (∀ p ∈ Φ0, p ∈ Φfull) →
      (∀ (name : Expression.Ident) ty dv mty, Imperative.PathConditionEntry.varDecl name ty dv ∈ es →
        ty.toMonoType? = some mty → (name.name, mty) ∈ Φfull) →
      ∀ entry ∈ es,
        (∀ l e, entry = .assumption l e → LExpr.HasSimpType Φfull Ψ [] e (.tcons "bool" [])) ∧
        (∀ (name : Expression.Ident) ty e, entry = .varDecl name ty (.det e) →
          ∃ mty, ty.toMonoType? = some mty ∧ LExpr.HasSimpType Φfull Ψ [] e mty) ∧
        (∀ l es', entry = .distinct l es' →
          2 ≤ es'.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es', LExpr.HasSimpType Φfull Ψ [] e τ) := by
  intro es
  induction es with
  | nil => intro Φ0 _ _ _ entry hentry; simp at hentry
  | cons entry rest ih =>
    intro Φ0 hwf hΦ0 hvd entry' hentry'
    obtain ⟨hpc, hrest⟩ := hwf.consInv
    rcases List.mem_cons.mp hentry' with rfl | hmem
    · refine ⟨?_, ?_, ?_⟩
      · intro l e heq; subst heq
        exact HasSimpType.weaken_fvar hΦ0 hpc.asmWitness
      · intro name ty e heq; subst heq
        obtain ⟨mty, hmono, hty⟩ := hpc.detWitness
        exact ⟨mty, hmono, HasSimpType.weaken_fvar hΦ0 hty⟩
      · intro l es' heq; subst heq
        obtain ⟨τ, hbase, hall⟩ := hpc.dstWitness
        exact ⟨hpc.dstLen, τ, hbase, fun e he => HasSimpType.weaken_fvar hΦ0 (hall e he)⟩
    · refine ih (stepCtx Φ0 entry) hrest ?_ ?_ entry' hmem
      · intro p hp
        cases entry with
        | assumption _ _ => exact hΦ0 p hp
        | varDecl name ty dv =>
          simp only [stepCtx] at hp
          split at hp
          · rename_i mty hmty
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hvd name ty dv mty List.mem_cons_self hmty
            · exact hΦ0 p hp'
          · exact hΦ0 p hp
        | distinct _ _ => exact hΦ0 p hp
      · intro name ty dv mty hin hmono
        exact hvd name ty dv mty (List.mem_cons_of_mem _ hin) hmono

/-- Each collected assumption / distinct-group comes from a corresponding path-condition entry. -/
theorem foldl_oblStep_entry :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (c : CoreCtx),
      (∀ e ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).assumptions,
          e ∈ c.assumptions ∨ ∃ l, Imperative.PathConditionEntry.assumption l e ∈ es) ∧
      (∀ g ∈ (es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).distincts,
          g ∈ c.distincts ∨ ∃ l, Imperative.PathConditionEntry.distinct l g ∈ es) := by
  intro es
  induction es with
  | nil => intro c; exact ⟨fun e h => Or.inl h, fun g h => Or.inl h⟩
  | cons entry rest ih =>
    intro c
    cases entry with
    | assumption l a =>
      obtain ⟨iha, ihd⟩ := ih { c with assumptions := c.assumptions ++ [a] }
      refine ⟨fun e he => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons] at *
      · rcases iha e he with h | ⟨l', h⟩
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact Or.inl h
          · exact Or.inr ⟨l, List.mem_cons_self⟩
        · exact Or.inr ⟨l', List.mem_cons_of_mem _ h⟩
      · rcases ihd g hg with h | ⟨l', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨l', List.mem_cons_of_mem _ h⟩
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none =>
          obtain ⟨iha, ihd⟩ := ih c
          refine ⟨fun x hx => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons, hm] at *
          · exact (iha x hx).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
          · exact (ihd g hg).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
        | some mty =>
          obtain ⟨iha, ihd⟩ := ih { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
          refine ⟨fun x hx => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons, hm] at *
          · exact (iha x hx).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
          · exact (ihd g hg).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          obtain ⟨iha, ihd⟩ := ih c
          refine ⟨fun x hx => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons, hm] at *
          · exact (iha x hx).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
          · exact (ihd g hg).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
        | some mty =>
          obtain ⟨iha, ihd⟩ := ih { c with varDecls := c.varDecls ++ [(name.name, mty)] }
          refine ⟨fun x hx => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons, hm] at *
          · exact (iha x hx).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
          · exact (ihd g hg).imp id (fun ⟨l', h⟩ => ⟨l', List.mem_cons_of_mem _ h⟩)
    | distinct l es' =>
      obtain ⟨iha, ihd⟩ := ih { c with distincts := c.distincts ++ [es'] }
      refine ⟨fun e he => ?_, fun g hg => ?_⟩ <;> simp only [List.foldl_cons] at *
      · rcases iha e he with h | ⟨l', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨l', List.mem_cons_of_mem _ h⟩
      · rcases ihd g hg with h | ⟨l', h⟩
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact Or.inl h
          · exact Or.inr ⟨l, List.mem_cons_self⟩
        · exact Or.inr ⟨l', List.mem_cons_of_mem _ h⟩

/-- The `VarDef`→`(name, ty)` map used by `CoreCtx.toΦ`/`VarDefsWF`. -/
private abbrev varDefSig (v : VarDef) : String × LMonoTy := (v.name, v.ty)

/-- Append one well-typed `varDef` at the END of an order-aware `VarDefsWF` chain (RHS typed against the
    full accumulated free-var prefix `Φ0 ++ varDefs`). -/
theorem VarDefsWF_snoc {Ψ : FnCtx} :
    ∀ (Φ0 : FVarCtx) (varDefs : List VarDef) (v : VarDef),
      VarDefsWF Ψ Φ0 varDefs →
      LExpr.HasSimpType (Φ0 ++ varDefs.map varDefSig) Ψ [] v.body v.ty →
      VarDefsWF Ψ Φ0 (varDefs ++ [v]) := by
  intro Φ0 varDefs
  induction varDefs generalizing Φ0 with
  | nil =>
    intro v h hbody
    simp only [List.map_nil, List.append_nil] at hbody
    exact VarDefsWF.cons hbody VarDefsWF.nil
  | cons v' rest ih =>
    intro v h hbody
    cases h with
    | @cons _ _ _ hty' hrestWF =>
      rw [List.cons_append]
      refine VarDefsWF.cons hty' (ih (Φ0 ++ [varDefSig v']) v hrestWF ?_)
      simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using hbody

/-- Narrow a `VarDefsWF` chain's function context from `factoryFnCtx F tf` to a sub-context `Ψ'` containing
    every varDef body's non-predefined op-heads (name-level, via reachability + factory functionality). -/
theorem VarDefsWF_restrict {F : Lambda.Factory CoreLParams} {Ψ' : FnCtx} (hsub : Ψ' ⊆ factoryFnCtx F tf) :
    ∀ (Φ0 : FVarCtx) (varDefs : List VarDef),
      VarDefsWF (factoryFnCtx F tf) Φ0 varDefs →
      (∀ v ∈ varDefs, ∀ p ∈ exprFnOps v.body, isPredefinedOp p.1 = false → p.1 ∈ Ψ'.map Prod.fst) →
      VarDefsWF Ψ' Φ0 varDefs := by
  intro Φ0 varDefs h
  induction h with
  | nil => intro _; exact VarDefsWF.nil
  | @cons Φ v rest hty hrestWF ih =>
    intro hused
    refine VarDefsWF.cons (HasSimpType.restrict_fn (fun p hp hnpre =>
      exprFnOps_pair_mem_of_name hsub (hasSimpType_fnOps_mem hty p hp hnpre)
        (hused v List.mem_cons_self p hp hnpre)) hty) (ih ?_)
    intro v' hv' p hp hnpre; exact hused v' (List.mem_cons_of_mem _ hv') p hp hnpre

/-- The obligation-partition fold only grows `varDecls`. -/
theorem foldl_oblStep_varDecls_mono :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (c : CoreCtx) {p : String × LMonoTy},
      p ∈ c.varDecls →
      p ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls := by
  intro es
  induction es with
  | nil => intro c p h; exact h
  | cons entry rest ih =>
    intro c p h
    rw [List.foldl_cons]
    apply ih
    cases entry with
    | assumption _ _ => exact h
    | varDecl name ty dv =>
      cases dv with
      | det e => cases hm : ty.toMonoType? <;> simp only [hm] <;> exact h
      | nondet =>
        cases hm : ty.toMonoType? with
        | none => simp only [hm]; exact h
        | some mty => simp only [hm]; exact List.mem_append_left _ h
    | distinct _ _ => exact h

/-- A monomorphic nondet `.varDecl` contributes its `(name, mty)` to the partition's `varDecls`. -/
theorem mem_obligationBaseCtx_varDecls (d : Imperative.ProofObligation Expression)
    {name : Expression.Ident} {ty : Expression.Ty} {mty : LMonoTy}
    (hmem : Imperative.PathConditionEntry.varDecl name ty .nondet ∈ d.assumptions.flatten)
    (hmono : ty.toMonoType? = some mty) :
    (name.name, mty) ∈ (obligationBaseCtx d).varDecls := by
  have key : ∀ (es : List (Imperative.PathConditionEntry Expression)) (c : CoreCtx),
      Imperative.PathConditionEntry.varDecl name ty .nondet ∈ es →
      (name.name, mty) ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls := by
    intro es
    induction es with
    | nil => intro c hmem'; simp at hmem'
    | cons entry rest ih =>
      intro c hmem'
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem' with rfl | hmem''
      · apply foldl_oblStep_varDecls_mono
        simp only [hmono]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · exact ih _ hmem''
  exact key d.assumptions.flatten {} hmem

/-- **The order-aware `VarDefsWF` construction** (at `factoryFnCtx`): folds the obligation partition,
    appending each det-var body (`VarDefsWF_snoc`) typed at the accumulated prefix `varDecls ++ (varDefs so
    far)` — obtained by weakening the entry's `PathEntryWF` prefix typing (`stepCtx` order ⊆ this prefix). -/
theorem obligation_VarDefsWF_aux {F : Lambda.Factory CoreLParams} (varDecls : FVarCtx) :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (c : CoreCtx),
      PathEntriesWF (factoryFnCtx F tf) Φ0 es →
      (∀ (name : Expression.Ident) ty mty, Imperative.PathConditionEntry.varDecl name ty .nondet ∈ es →
        ty.toMonoType? = some mty → (name.name, mty) ∈ varDecls) →
      (∀ p ∈ Φ0, p ∈ varDecls ++ c.varDefs.map varDefSig) →
      VarDefsWF (factoryFnCtx F tf) varDecls c.varDefs →
      VarDefsWF (factoryFnCtx F tf) varDecls
        ((es.foldl (fun c entry => match entry with
          | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
          | .varDecl name ty (.det e) => match ty.toMonoType? with
              | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
              | none => c
          | .varDecl name ty .nondet => match ty.toMonoType? with
              | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
              | none => c
          | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs) := by
  intro es
  induction es with
  | nil => intro Φ0 c _ _ _ hwf; exact hwf
  | cons entry rest ih =>
    intro Φ0 c hpew hnondet hinv hwf
    obtain ⟨hpc, hrest⟩ := hpew.consInv
    have hnondet' : ∀ (name : Expression.Ident) ty mty,
        Imperative.PathConditionEntry.varDecl name ty .nondet ∈ rest →
        ty.toMonoType? = some mty → (name.name, mty) ∈ varDecls :=
      fun name ty mty hin hmono => hnondet name ty mty (List.mem_cons_of_mem _ hin) hmono
    cases entry with
    | assumption l a =>
      simp only [List.foldl_cons]
      exact ih _ _ hrest hnondet' (fun p hp => hinv p hp) hwf
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest hnondet' ?_ hwf
          intro p hp; simp only [stepCtx, hm] at hp; exact hinv p hp
        | some mty =>
          obtain ⟨mty', hmono', hty'⟩ := hpc.detWitness
          rw [hm] at hmono'; injection hmono' with hmtyeq; subst hmtyeq
          have hbody : LExpr.HasSimpType (varDecls ++ c.varDefs.map varDefSig) (factoryFnCtx F tf) []
              e mty := HasSimpType.weaken_fvar hinv hty'
          have hwf' : VarDefsWF (factoryFnCtx F tf) varDecls
              (c.varDefs ++ [(⟨name.name, mty, e⟩ : VarDef)]) :=
            VarDefsWF_snoc varDecls c.varDefs ⟨name.name, mty, e⟩ hwf hbody
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest hnondet' ?_ hwf'
          intro p hp
          simp only [stepCtx, hm] at hp
          simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
            List.mem_append, List.mem_singleton]
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Or.inr rfl
          · exact Or.inl (List.mem_append.mp (hinv p hp'))
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest hnondet' ?_ hwf
          intro p hp; simp only [stepCtx, hm] at hp; exact hinv p hp
        | some mty =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest hnondet' ?_ hwf
          intro p hp
          simp only [stepCtx, hm] at hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact List.mem_append_left _ (hnondet name ty mty List.mem_cons_self hm)
          · exact hinv p hp'
    | distinct l es' =>
      simp only [List.foldl_cons]
      exact ih _ _ hrest hnondet' (fun p hp => hinv p hp) hwf

/-- Every `factoryFnCtx` name is non-predefined (it ranges over `Factory.nonPredefined`, the
    `!isPredefinedOp`-filtered user functions). -/
theorem factoryFnCtx_names_notPredefined {F : Lambda.Factory CoreLParams} :
    ∀ nm ∈ (factoryFnCtx F tf).map Prod.fst, isPredefinedOp nm = false := by
  intro nm h
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
  obtain ⟨f, hf, hfeq⟩ := List.mem_map.mp hp
  subst hfeq
  rw [← hpn]
  simpa using (mem_nonPredefined.mp hf).2.1

/-- Inserting a fresh element into the middle of a `Nodup` append preserves `Nodup`. -/
theorem nodup_append_cons_of_notMem {α : Type} {A B : List α} {x : α}
    (hnd : (A ++ B).Nodup) (hx : x ∉ A ++ B) : (A ++ x :: B).Nodup :=
  (List.perm_middle (a := x) (l₁ := A) (l₂ := B)).symm.nodup (List.nodup_cons.mpr ⟨hx, hnd⟩)

/-- The obligation-partition variable names (`varDecls` nondet ++ `varDefs` det) are `Nodup` and disjoint
    from the factory function names — each `PathEntryWF` var name is fresh wrt (accumulated fvars ++
    factory names), and the accumulated var names are ⊆ the threaded `Φ0`. -/
theorem oblStep_toΦ_nodup {F : Lambda.Factory CoreLParams} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (c : CoreCtx),
      PathEntriesWF (factoryFnCtx F tf) Φ0 es →
      (c.varDecls.map Prod.fst ++ c.varDefs.map (·.name)).Nodup →
      (∀ nm ∈ c.varDecls.map Prod.fst ++ c.varDefs.map (·.name), nm ∈ Φ0.map Prod.fst) →
      (∀ nm ∈ c.varDecls.map Prod.fst ++ c.varDefs.map (·.name),
        nm ∉ (factoryFnCtx F tf).map Prod.fst) →
      ((es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls.map Prod.fst ++
       (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs.map (·.name)).Nodup ∧
      (∀ nm ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls.map Prod.fst ++
       (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs.map (·.name),
        nm ∉ (factoryFnCtx F tf).map Prod.fst) := by
  intro es
  induction es with
  | nil => intro Φ0 c _ hnd _ hnotfac; exact ⟨hnd, hnotfac⟩
  | cons entry rest ih =>
    intro Φ0 c hpew hnd hsub hnotfac
    obtain ⟨hpc, hrest⟩ := hpew.consInv
    cases entry with
    | assumption l a => simp only [List.foldl_cons]; exact ih _ _ hrest hnd hsub hnotfac
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [List.foldl_cons, hm]
          exact ih _ _ hrest hnd
            (fun nm hnm => by simp only [stepCtx, hm]; exact hsub nm hnm) hnotfac
        | some mty =>
          have hfresh : name.name ∉ (Φ0 ++ factoryFnCtx F tf).map Prod.fst := by
            cases hpc with | varDeclDet _ _ _ hfr _ => exact hfr
          rw [List.map_append, List.mem_append] at hfresh
          have hΦ0fresh : name.name ∉ Φ0.map Prod.fst := fun hc => hfresh (Or.inl hc)
          have hfacfresh : name.name ∉ (factoryFnCtx F tf).map Prod.fst := fun hc => hfresh (Or.inr hc)
          have hx : name.name ∉ c.varDecls.map Prod.fst ++ c.varDefs.map (·.name) :=
            fun hc => hΦ0fresh (hsub name.name hc)
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest ?_ ?_ ?_
          · -- nodup: φnames' = (decls names) ++ (defs names ++ [name.name]) = φnames ++ [name.name]
            simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
            exact nodup_append_cons_of_notMem (B := []) (by simpa using hnd) (by simpa using hx)
          · -- subset of new Φ0 = (name.name,mty) :: Φ0
            intro nm hnm
            simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
              List.mem_append, List.mem_singleton] at hnm
            simp only [stepCtx, hm, List.map_cons, List.mem_cons]
            rcases hnm with hnm | rfl
            · exact Or.inr (hsub nm (List.mem_append.mpr hnm))
            · exact Or.inl rfl
          · intro nm hnm
            simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
              List.mem_append, List.mem_singleton] at hnm
            rcases hnm with hnm | rfl
            · exact hnotfac nm (List.mem_append.mpr hnm)
            · exact hfacfresh
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [List.foldl_cons, hm]
          exact ih _ _ hrest hnd
            (fun nm hnm => by simp only [stepCtx, hm]; exact hsub nm hnm) hnotfac
        | some mty =>
          have hfresh : name.name ∉ (Φ0 ++ factoryFnCtx F tf).map Prod.fst := by
            cases hpc with | varDeclNondet _ _ hfr _ => exact hfr
          rw [List.map_append, List.mem_append] at hfresh
          have hΦ0fresh : name.name ∉ Φ0.map Prod.fst := fun hc => hfresh (Or.inl hc)
          have hfacfresh : name.name ∉ (factoryFnCtx F tf).map Prod.fst := fun hc => hfresh (Or.inr hc)
          have hx : name.name ∉ c.varDecls.map Prod.fst ++ c.varDefs.map (·.name) :=
            fun hc => hΦ0fresh (hsub name.name hc)
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest ?_ ?_ ?_
          · -- nodup: φnames' = (decls names ++ [name.name]) ++ defs names = D ++ name.name :: Fs
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append]
            exact nodup_append_cons_of_notMem hnd hx
          · intro nm hnm
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append, List.mem_append, List.mem_cons] at hnm
            simp only [stepCtx, hm, List.map_cons, List.mem_cons]
            rcases hnm with hnm | rfl | hnm
            · exact Or.inr (hsub nm (List.mem_append.mpr (Or.inl hnm)))
            · exact Or.inl rfl
            · exact Or.inr (hsub nm (List.mem_append.mpr (Or.inr hnm)))
          · intro nm hnm
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append, List.mem_append, List.mem_cons] at hnm
            rcases hnm with hnm | rfl | hnm
            · exact hnotfac nm (List.mem_append.mpr (Or.inl hnm))
            · exact hfacfresh
            · exact hnotfac nm (List.mem_append.mpr (Or.inr hnm))
    | distinct l es' => simp only [List.foldl_cons]; exact ih _ _ hrest hnd hsub hnotfac

/-- The user-function-context NAMES of a collected `CoreCtx` (`fnDecls` ++ `fnDefs`, name-projected). -/
private def ψnames (c : CoreCtx) : List String := c.fnDecls.map Prod.fst ++ c.fnDefs.map (·.name)

/-- `toΨ`'s name projection is exactly `ψnames` (the arrow annotation drops under `Prod.fst`). -/
theorem toΨ_map_fst_eq_ψnames (c : CoreCtx) : c.toΨ.map Prod.fst = ψnames c := by
  unfold CoreCtx.toΨ ψnames
  rw [List.map_append, List.map_map]; rfl

/-- `addFunc` inserts exactly one new name (`g.name.name`) into `ψnames` (as a `Perm`) — it appends to
    either `fnDecls` (declare) or `fnDefs` (define). -/
theorem ψnames_addFunc_perm (st : CollectState) (g : LFunc CoreLParams) :
    (ψnames (st.addFunc g).ctx).Perm (g.name.name :: ψnames st.ctx) := by
  unfold ψnames CollectState.addFunc
  split
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← List.append_assoc]
    exact List.perm_append_comm
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.append_assoc, List.singleton_append]
    exact List.perm_middle

/-- `addFunc` preserves `ψnames` nodup, given the new name is fresh. -/
theorem ψnames_addFunc_nodup (st : CollectState) (g : LFunc CoreLParams)
    (hnd : (ψnames st.ctx).Nodup) (hx : g.name.name ∉ ψnames st.ctx) :
    (ψnames (st.addFunc g).ctx).Nodup :=
  (ψnames_addFunc_perm st g).symm.nodup (List.nodup_cons.mpr ⟨hx, hnd⟩)

/-- Membership in `addFunc`'s `ψnames` is either the new name or an old one. -/
theorem mem_ψnames_addFunc (st : CollectState) (g : LFunc CoreLParams) {nm : String}
    (h : nm ∈ ψnames (st.addFunc g).ctx) : nm = g.name.name ∨ nm ∈ ψnames st.ctx :=
  List.mem_cons.mp ((ψnames_addFunc_perm st g).mem_iff.mp h)

/-- **The materialize fold produces `Nodup` `ψnames`.** Over a name-`Nodup` worklist, each guarded
    `addFunc` adds a name absent from the accumulated `ψnames` (the disjointness invariant: accumulated
    names avoid the remaining worklist). -/
theorem foldl_matStep_ψnames_nodup :
    ∀ (l : List (LFunc CoreLParams)) (st : CollectState),
      (l.map (·.name.name)).Nodup →
      (ψnames st.ctx).Nodup →
      (∀ nm ∈ ψnames st.ctx, nm ∉ l.map (·.name.name)) →
      (ψnames (l.foldl (fun s g =>
        if s.seenFns.contains g.name.name then s.addFunc g else s) st).ctx).Nodup := by
  intro l
  induction l with
  | nil => intro st _ hψ _; exact hψ
  | cons g rest ih =>
    intro st hlnd hψ hdisj
    rw [List.map_cons] at hlnd
    have hlnd' := List.nodup_cons.mp hlnd
    rw [List.foldl_cons]
    by_cases h : st.seenFns.contains g.name.name = true
    · rw [if_pos h]
      have hgx : g.name.name ∉ ψnames st.ctx :=
        fun hc => hdisj g.name.name hc (by simp)
      refine ih (st.addFunc g) hlnd'.2 (ψnames_addFunc_nodup st g hψ hgx) ?_
      intro nm hnm hc
      rcases mem_ψnames_addFunc st g hnm with rfl | hmem
      · exact hlnd'.1 hc
      · exact hdisj nm hmem (List.mem_cons_of_mem _ hc)
    · rw [if_neg h]
      exact ih st hlnd'.2 hψ (fun nm hnm hc => hdisj nm hnm (List.mem_cons_of_mem _ hc))

/-- No `factoryFnCtx` name is a reserved quantifier binder `$__bv{n}` (each user function carries
    `fnNameNotReserved` from `Factory.SimpWF`). -/
theorem factoryFnCtx_name_notReserved {F : Lambda.Factory CoreLParams} (hsimp : Factory.SimpWF F tf) :
    ∀ nm ∈ (factoryFnCtx F tf).map Prod.fst, ∀ n : Nat, nm ≠ s!"$__bv{n}" := by
  intro nm h n
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
  obtain ⟨f, hf, hfeq⟩ := List.mem_map.mp hp
  subst hfeq
  rw [← hpn]
  exact (hsimp.fnsSigSimp f hf).fnNameNotReserved n

/-- No obligation-partition variable name (`varDecls` nondet or `varDefs` det) is a reserved `$__bv{n}`
    binder — each comes from a `PathEntryWF` carrying the reserved-name hygiene field. -/
theorem oblStep_varNames_not_reserved {Ψ : FnCtx} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (c : CoreCtx),
      PathEntriesWF Ψ Φ0 es →
      (∀ p ∈ c.varDecls, ∀ n : Nat, p.1 ≠ s!"$__bv{n}") →
      (∀ v ∈ c.varDefs, ∀ n : Nat, v.name ≠ s!"$__bv{n}") →
      (∀ p ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls,
        ∀ n : Nat, p.1 ≠ s!"$__bv{n}") ∧
      (∀ v ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs,
        ∀ n : Nat, v.name ≠ s!"$__bv{n}") := by
  intro es
  induction es with
  | nil => intro Φ0 c _ hdec hvd; exact ⟨hdec, hvd⟩
  | cons entry rest ih =>
    intro Φ0 c hpew hdec hvd
    obtain ⟨hpc, hrest⟩ := hpew.consInv
    cases entry with
    | assumption l a => simp only [List.foldl_cons]; exact ih _ _ hrest hdec hvd
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none => simp only [List.foldl_cons, hm]; exact ih _ _ hrest hdec hvd
        | some mty =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest hdec ?_
          intro v hv m
          rcases List.mem_append.mp hv with hv' | hv'
          · exact hvd v hv' m
          · rw [List.mem_singleton] at hv'; subst hv'
            cases hpc with | varDeclDet _ _ _ _ hnr => exact hnr m
      | nondet =>
        cases hm : ty.toMonoType? with
        | none => simp only [List.foldl_cons, hm]; exact ih _ _ hrest hdec hvd
        | some mty =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest ?_ hvd
          intro p hp m
          rcases List.mem_append.mp hp with hp' | hp'
          · exact hdec p hp' m
          · rw [List.mem_singleton] at hp'; subst hp'
            cases hpc with | varDeclNondet _ _ _ hnr => exact hnr m
    | distinct l es' => simp only [List.foldl_cons]; exact ih _ _ hrest hdec hvd

/-- A base monotype (bool/int/string/bitvec — never `arrow`) is its own `collectArrowTy` return with no
    argument types. -/
theorem collectArrowTy_of_base {ret : LMonoTy} (h : LExpr.MonoTyIsBase ret) :
    collectArrowTy ret = ([], ret) := by
  cases h <;> rfl

/-- `collectArrowTy` inverts `foldr arrow` when the return type is base (so it isn't peeled further). -/
theorem collectArrowTy_foldr_base :
    ∀ (args : List LMonoTy) (ret : LMonoTy), LExpr.MonoTyIsBase ret →
      collectArrowTy (List.foldr LMonoTy.arrow ret args) = (args, ret) := by
  intro args
  induction args with
  | nil => intro ret hret; exact collectArrowTy_of_base hret
  | cons a rest ih =>
    intro ret hret
    simp only [List.foldr, LMonoTy.arrow, collectArrowTy, ih ret hret]

/-- Every `varDecls` pair the obligation partition accumulates is base-typed — the added nondet monotype
    is base by its `PathEntryWF` (`varDeclNondet`). -/
theorem oblStep_varDecls_base {Ψ : FnCtx} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx) (c : CoreCtx),
      PathEntriesWF Ψ Φ0 es →
      (∀ p ∈ c.varDecls, LExpr.MonoTyIsBase p.2) →
      ∀ p ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDecls,
        LExpr.MonoTyIsBase p.2 := by
  intro es
  induction es with
  | nil => intro Φ0 c _ hbase p hp; exact hbase p hp
  | cons entry rest ih =>
    intro Φ0 c hpew hbase
    obtain ⟨hpc, hrest⟩ := hpew.consInv
    cases entry with
    | assumption l a => simp only [List.foldl_cons]; exact ih _ _ hrest hbase
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none => simp only [List.foldl_cons, hm]; exact ih _ _ hrest hbase
        | some mty => simp only [List.foldl_cons, hm]; exact ih _ _ hrest hbase
      | nondet =>
        cases hm : ty.toMonoType? with
        | none => simp only [List.foldl_cons, hm]; exact ih _ _ hrest hbase
        | some mty =>
          simp only [List.foldl_cons, hm]
          refine ih _ _ hrest ?_
          intro p hp
          rcases List.mem_append.mp hp with hp' | hp'
          · exact hbase p hp'
          · rw [List.mem_singleton] at hp'; subst hp'
            cases hpc with
            | varDeclNondet hmono' hbase' _ _ =>
              rw [hm] at hmono'; injection hmono' with h; subst h; exact hbase'
    | distinct l es' => simp only [List.foldl_cons]; exact ih _ _ hrest hbase

/-- **Collect well-formedness.** A well-formed obligation over a simp-WF function factory collects into
    a well-formed, name-hygienic `CoreCtx`. No datatype-op disjointness hypothesis is needed: the user
    function context `factoryFnCtx F tf` excludes datatype ops by construction (`nonPredefined` filters
    them), so `factoryFnCtx_notDatatypeOp` discharges what the reachability walk requires. -/
theorem collect_WF
    -- ── source side ──
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    -- ── correspondence ──
    {uAT : Bool} :
    CoreCtx.WF (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) d.obligation ∧
    CoreCtx.NamesWF (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) uAT := by
  -- Reachability (op-heads of every collected expression land in the collected `toΨ`).
  have hreach := obligation_fnOps_reachable (uAT := uAT) (karities := karities) d hpwf hsimp
  have hΨsub : (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ ⊆ factoryFnCtx F tf :=
    collectObligation_toΨ_subset hpwf hsimp
  -- Seen ⟹ nonPredefined (for `fnAxioms` typing).
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hpwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  -- Front-seed collapses (`unmanagedFVars d = []`), pinning the collected chunks to the raw partition.
  have hnil : unmanagedFVars d = [] := unmanagedFVars_eq_nil_of_WF hpwf
  have hvarDecls : (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).varDecls
      = (obligationBaseCtx d).varDecls :=
    collectObligation_proj d (·.varDecls) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun s f => by unfold CollectState.addFunc; split <;> rfl) (fun _ _ => rfl)
      (by rw [hnil, List.nil_append])
  obtain ⟨hassum, hdist, hvarDefs⟩ := collectObligation_chunks (uAT := uAT) (tf := tf)
    (karities := karities) d
  -- Every accumulated free-var pair is in the collected `toΦ`.
  have hToΦmem : ∀ p ∈ accumFVarCtx d.assumptions.flatten,
      p ∈ (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ := by
    intro p hp
    unfold CoreCtx.toΦ
    rw [hvarDecls, hvarDefs]
    exact accumFVarCtx_sub_obligationBaseCtx_toΦ d p hp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- fnDeclsSigBase
  · intro nm τ hmem
    obtain ⟨f, hf, hfseen, hpe⟩ := collectObligation_fnDecls_mem d (nm, τ) hmem
    rw [Prod.mk.injEq] at hpe; obtain ⟨hnm, hτ⟩ := hpe; subst hτ
    have hsimpSig := hsimp.fnsSigSimp f (f_nonPred f hf hfseen)
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [collectArrowTy_foldr_base f.inputs.values f.output hsimpSig.fnRetBase] at ha
      exact hsimpSig.fnArgsBase a ha
    · rw [collectArrowTy_foldr_base f.inputs.values f.output hsimpSig.fnRetBase]
      exact hsimpSig.fnRetBase
  -- fnDefsWF
  · exact collectObligation_fnDefsWF hpwf hsimp
  -- varDeclsSigBase
  · intro nm τ hmem
    rw [hvarDecls] at hmem
    have hbase : LExpr.MonoTyIsBase τ :=
      oblStep_varDecls_base d.assumptions.flatten [] {} hpwf.entriesWF
        (by intro p hp; simp at hp) (nm, τ) hmem
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [collectArrowTy_of_base hbase] at ha; simp at ha
    · rw [collectArrowTy_of_base hbase]; exact hbase
  -- varDefsWF
  · have hvdFac : VarDefsWF (factoryFnCtx F tf)
        (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).varDecls
        (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).varDefs := by
      rw [hvarDefs]
      exact obligation_VarDefsWF_aux _ d.assumptions.flatten [] {} hpwf.entriesWF
        (fun name ty mty hin hmono => by
          rw [hvarDecls]; exact mem_obligationBaseCtx_varDecls d hin hmono)
        (by intro p hp; simp at hp) VarDefsWF.nil
    exact VarDefsWF_restrict hΨsub _ _ hvdFac hreach.2.1
  -- fnAxiomsWF
  · intro e he
    obtain ⟨f, hf, hfseen, hea⟩ := collectObligation_fnAxioms_mem d e he
    have hax : LExpr.HasSimpType [] (factoryFnCtx F tf) [] e (.tcons "bool" []) :=
      hsimp.fnAxiomsWF f (f_nonPred f hf hfseen) e hea
    have hty : LExpr.HasSimpType (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ
        (factoryFnCtx F tf) [] e (.tcons "bool" []) :=
      HasSimpType.weaken_fvar (by intro p hp; simp at hp) hax
    refine HasSimpType.restrict_fn ?_ hty
    intro p hp hnpre
    exact exprFnOps_pair_mem_of_name hΨsub (hasSimpType_fnOps_mem hty p hp hnpre)
      (hreach.2.2.2.2.1 e he p hp hnpre)
  -- assumptionsWF
  · intro e he
    have he' : e ∈ (obligationBaseCtx d).assumptions := hassum ▸ he
    rcases (foldl_oblStep_entry d.assumptions.flatten {}).1 e he' with h | ⟨l, hain⟩
    · simp at h
    · have htyd := (pathEntriesWF_flatMap_typed_accum (accumFVarCtx d.assumptions.flatten)
        d.assumptions.flatten [] hpwf.entriesWF (by intro p hp; simp at hp)
        (fun name ty dv mty hin hmono =>
          mem_accumFVarCtx d.assumptions.flatten [] name ty dv mty hin hmono)
        (.assumption l e) hain).1 l e rfl
      have hty : LExpr.HasSimpType (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ
          (factoryFnCtx F tf) [] e (.tcons "bool" []) := HasSimpType.weaken_fvar hToΦmem htyd
      refine HasSimpType.restrict_fn ?_ hty
      intro p hp hnpre
      exact exprFnOps_pair_mem_of_name hΨsub (hasSimpType_fnOps_mem hty p hp hnpre)
        (hreach.1 e he p hp hnpre)
  -- distinctsWF
  · intro es hes
    have hes' : es ∈ (obligationBaseCtx d).distincts := hdist ▸ hes
    rcases (foldl_oblStep_entry d.assumptions.flatten {}).2 es hes' with h | ⟨l, hdin⟩
    · simp at h
    · have htyd := (pathEntriesWF_flatMap_typed_accum (accumFVarCtx d.assumptions.flatten)
        d.assumptions.flatten [] hpwf.entriesWF (by intro p hp; simp at hp)
        (fun name ty dv mty hin hmono =>
          mem_accumFVarCtx d.assumptions.flatten [] name ty dv mty hin hmono)
        (.distinct l es) hdin).2.2 l es rfl
      obtain ⟨hlen, τ, hbaseτ, hall⟩ := htyd
      refine ⟨hlen, τ, hbaseτ, fun e hee => ?_⟩
      have hty : LExpr.HasSimpType (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ
          (factoryFnCtx F tf) [] e τ := HasSimpType.weaken_fvar hToΦmem (hall e hee)
      refine HasSimpType.restrict_fn ?_ hty
      intro p hp hnpre
      exact exprFnOps_pair_mem_of_name hΨsub (hasSimpType_fnOps_mem hty p hp hnpre)
        (hreach.2.2.1 es hes e hee p hp hnpre)
  -- goalWF
  · have hty : LExpr.HasSimpType (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ
        (factoryFnCtx F tf) [] d.obligation (.tcons "bool" []) :=
      HasSimpType.weaken_fvar hToΦmem hpwf.goalWF
    refine HasSimpType.restrict_fn ?_ hty
    intro p hp hnpre
    exact exprFnOps_pair_mem_of_name hΨsub (hasSimpType_fnOps_mem hty p hp hnpre)
      (hreach.2.2.2.2.2 p hp hnpre)
  -- datatypesEmpty
  · exact (collectObligation_datatypeFree_of_WF hpwf hsimp).1
  -- datatypeFunsEmpty
  · exact (collectObligation_datatypeFree_of_WF hpwf hsimp).2
  -- NamesWF
  · refine ⟨?_, ?_, ?_⟩
    -- names_nodup
    · -- `toΨ` names: nodup via the materialize fold over the nodup factory names.
      have h1 : (collectFuncsState uAT F tf d).ctx.fnDecls = [] := by
        rw [foldl_ctx_proj (·.fnDecls) (fun s e => by rw [collectFuncs_ctx])]
        exact obligationBaseCtx_fnDecls_nil d
      have h2 : (collectFuncsState uAT F tf d).ctx.fnDefs = [] := by
        rw [foldl_ctx_proj (·.fnDefs) (fun s e => by rw [collectFuncs_ctx])]
        exact obligationBaseCtx_fnDefs_nil d
      have hemptyψ : ψnames (collectFuncsState uAT F tf d).ctx = [] := by
        unfold ψnames; rw [h1, h2]; rfl
      have hΨnodup :
          ((collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΨ.map Prod.fst).Nodup := by
        rw [collectObligation_toΨ_map_eq, toΨ_map_fst_eq_ψnames]
        unfold CollectState.materializeFuncs
        rw [← Array.foldl_toList]
        refine foldl_matStep_ψnames_nodup _ _ (Lambda.Factory.name_nodup F) ?_ ?_
        · rw [hemptyψ]; exact List.nodup_nil
        · intro nm hnm; rw [hemptyψ] at hnm; exact absurd hnm List.not_mem_nil
      -- `toΦ` names: nodup + factory-disjoint via the obligation-partition var-name threading.
      have hΦpair := oblStep_toΦ_nodup (F := F) d.assumptions.flatten [] {}
        hpwf.entriesWF (by simp) (by simp) (by simp)
      have hΦeq : (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d).toΦ.map Prod.fst
          = (obligationBaseCtx d).varDecls.map Prod.fst ++ (obligationBaseCtx d).varDefs.map (·.name) := by
        unfold CoreCtx.toΦ
        rw [hvarDecls, hvarDefs, List.map_append, List.map_map]; rfl
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨hΨnodup, ?_, ?_⟩
      · rw [hΦeq]; exact hΦpair.1
      · intro x hx b hb
        rw [hΦeq] at hb
        have hxfac : x ∈ (factoryFnCtx F tf).map Prod.fst := by
          obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hx
          exact List.mem_map.mpr ⟨p, hΨsub hp, hpn⟩
        intro heq; subst heq
        exact hΦpair.2 x hb hxfac
    -- names_no_reserved
    · intro n hcontra
      rw [List.map_append, List.mem_append] at hcontra
      rcases hcontra with hΨ | hΦ
      · have hfac : s!"$__bv{n}" ∈ (factoryFnCtx F tf).map Prod.fst := by
          obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hΨ
          exact List.mem_map.mpr ⟨p, hΨsub hp, hpn⟩
        exact factoryFnCtx_name_notReserved hsimp _ hfac n rfl
      · unfold CoreCtx.toΦ at hΦ
        rw [hvarDecls, hvarDefs, List.map_append, List.mem_append] at hΦ
        have hres := oblStep_varNames_not_reserved d.assumptions.flatten [] {}
          hpwf.entriesWF (by simp) (by simp)
        rcases hΦ with hd | hv
        · obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hd
          exact hres.1 p hp n hpn
        · obtain ⟨pair, hpair, hpn⟩ := List.mem_map.mp hv
          obtain ⟨v, hv', hveq⟩ := List.mem_map.mp hpair
          rw [← hveq] at hpn
          exact hres.2 v hv' n hpn
    -- fnNamesNotPredefined
    · intro nm hnm
      have hfac : nm ∈ (factoryFnCtx F tf).map Prod.fst := by
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hnm
        exact List.mem_map.mpr ⟨p, hΨsub hp, hpn⟩
      exact corePredefinedOp_none_of_notPredefined (factoryFnCtx_names_notPredefined nm hfac)

/-- Each collected `varDef` originates from a deterministic `.varDecl` path entry (or was pre-seeded). -/
theorem foldl_oblStep_varDef_entry :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (c : CoreCtx),
      ∀ v ∈ (es.foldl (fun c entry => match entry with
        | .assumption _ e => { c with assumptions := c.assumptions ++ [e] }
        | .varDecl name ty (.det e) => match ty.toMonoType? with
            | some mty => { c with varDefs := c.varDefs ++ [{ name := name.name, ty := mty, body := e }] }
            | none => c
        | .varDecl name ty .nondet => match ty.toMonoType? with
            | some mty => { c with varDecls := c.varDecls ++ [(name.name, mty)] }
            | none => c
        | .distinct _ es => { c with distincts := c.distincts ++ [es] }) c).varDefs,
        v ∈ c.varDefs ∨ ∃ (name : Expression.Ident) (ty : Expression.Ty),
          Imperative.PathConditionEntry.varDecl name ty (.det v.body) ∈ es ∧
          v.name = name.name ∧ ty.toMonoType? = some v.ty := by
  intro es
  induction es with
  | nil => intro c v hv; exact Or.inl hv
  | cons entry rest ih =>
    intro c v hv
    rw [List.foldl_cons] at hv
    cases entry with
    | assumption l a =>
      rcases ih _ v hv with h | ⟨name, ty, hin, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨name, ty, List.mem_cons_of_mem _ hin, h1, h2⟩
    | varDecl name ty dv =>
      cases dv with
      | det e =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [hm] at hv
          rcases ih _ v hv with h | ⟨n, t, hin, h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨n, t, List.mem_cons_of_mem _ hin, h1, h2⟩
        | some mty =>
          simp only [hm] at hv
          rcases ih _ v hv with h | ⟨n, t, hin, h1, h2⟩
          · rcases List.mem_append.mp h with h' | h'
            · exact Or.inl h'
            · rw [List.mem_singleton] at h'; subst h'
              exact Or.inr ⟨name, ty, List.mem_cons_self, rfl, hm⟩
          · exact Or.inr ⟨n, t, List.mem_cons_of_mem _ hin, h1, h2⟩
      | nondet =>
        cases hm : ty.toMonoType? with
        | none =>
          simp only [hm] at hv
          rcases ih _ v hv with h | ⟨n, t, hin, h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨n, t, List.mem_cons_of_mem _ hin, h1, h2⟩
        | some mty =>
          simp only [hm] at hv
          rcases ih _ v hv with h | ⟨n, t, hin, h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨n, t, List.mem_cons_of_mem _ hin, h1, h2⟩
    | distinct l es' =>
      rcases ih _ v hv with h | ⟨n, t, hin, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, t, List.mem_cons_of_mem _ hin, h1, h2⟩

/-- A `distinctDenote` Nodup verdict is independent of the (Φ,Ψ,witness) it was computed with — the base
    type is unique (`HasTypeA_unique`) and `simpDenote` is proof-irrelevant. -/
theorem distinctDenote_Nodup_congr {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp}
    {Φ1 Ψ1 Φ2 Ψ2 : _} {es : List Expression.Expr} {e0 : Expression.Expr} (he0 : e0 ∈ es)
    (hw1 : ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType Φ1 Ψ1 [] e τ)
    (hw2 : ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType Φ2 Ψ2 [] e τ)
    (H : (distinctDenote opInterp fvarVal (Φ := Φ1) (Ψ := Ψ1) es hw1).Nodup) :
    (distinctDenote opInterp fvarVal (Φ := Φ2) (Ψ := Ψ2) es hw2).Nodup := by
  have hτeq : hw2.choose = hw1.choose := HasTypeA_unique
    (HasSimpType_implies_HasTypeA (hw2.choose_spec.2 e0 he0))
    (HasSimpType_implies_HasTypeA (hw1.choose_spec.2 e0 he0))
  unfold distinctDenote at H ⊢
  exact pairwise_denote_congr hτeq H

/-- Extract each assumption entry's `⟦e⟧ = true` from the folded `ModelSatisfiesPCs`. -/
theorem ModelSatisfiesPCs_assumption {Ψ : FnCtx} {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx)
      (h : PathEntriesWF Ψ Φ0 es),
      ProofObligation.ModelSatisfiesPCs opInterp fvarVal es Φ0 h →
      ∀ (l : String) (e : Expression.Expr),
        Imperative.PathConditionEntry.assumption l e ∈ es →
        ∀ (hty : LExpr.HasTypeA [] e (.tcons "bool" [])),
          (simpDenote opInterp fvarVal .nil e (.tcons "bool" []) hty : Bool) = true := by
  intro es
  induction es with
  | nil => intro _ _ _ l e hin _; simp at hin
  | cons entry rest ih =>
    intro Φ0 h hms l e hin hty
    simp only [ProofObligation.ModelSatisfiesPCs] at hms
    obtain ⟨hpc, hrest⟩ := hms
    rcases List.mem_cons.mp hin with rfl | hmem
    · simp only [ProofObligation.ModelSatisfiesPC] at hpc; exact hpc
    · exact ih (stepCtx Φ0 entry) h.consInv.2 hrest l e hmem hty

/-- Transport a det-var consistency equation across equal monotypes (both are bound vars ⇒ `subst`). -/
theorem det_eq_congr {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} {name : String} {e : Expression.Expr}
    {τ₁ τ₂ : LMonoTy} (hτ : τ₁ = τ₂)
    {h₁ : LExpr.HasTypeA [] e τ₁} {h₂ : LExpr.HasTypeA [] e τ₂}
    (H : fvarVal ⟨name, ()⟩ (τ₁.substTyVars simpTyVarVal)
        = simpDenote opInterp fvarVal .nil e τ₁ h₁) :
    fvarVal ⟨name, ()⟩ (τ₂.substTyVars simpTyVarVal)
        = simpDenote opInterp fvarVal .nil e τ₂ h₂ := by
  subst hτ; exact H

/-- Extract each det-var entry's `fvarVal = ⟦body⟧` from the folded `ModelSatisfiesPCs`. -/
theorem ModelSatisfiesPCs_det {Ψ : FnCtx} {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx)
      (h : PathEntriesWF Ψ Φ0 es),
      ProofObligation.ModelSatisfiesPCs opInterp fvarVal es Φ0 h →
      ∀ (name : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr),
        Imperative.PathConditionEntry.varDecl name ty (.det e) ∈ es →
        ∀ (mty : LMonoTy), ty.toMonoType? = some mty → ∀ (hty : LExpr.HasTypeA [] e mty),
          fvarVal ⟨name.name, ()⟩ (mty.substTyVars simpTyVarVal)
          = simpDenote opInterp fvarVal .nil e mty hty := by
  intro es
  induction es with
  | nil => intro _ _ _ name ty e hin _ _ _; simp at hin
  | cons entry rest ih =>
    intro Φ0 h hms name ty e hin mty hmono hty
    simp only [ProofObligation.ModelSatisfiesPCs] at hms
    obtain ⟨hpc, hrest⟩ := hms
    rcases List.mem_cons.mp hin with rfl | hmem
    · simp only [ProofObligation.ModelSatisfiesPC] at hpc
      have hchoose : (h.consInv.1).detWitness.choose = mty :=
        Option.some.inj ((h.consInv.1).detWitness.choose_spec.1.symm.trans hmono)
      exact det_eq_congr hchoose hpc
    · exact ih (stepCtx Φ0 entry) h.consInv.2 hrest name ty e hmem mty hmono hty

/-- Extract each distinct group's Nodup verdict from the folded `ModelSatisfiesPCs` (at any target
    witness, via `distinctDenote_Nodup_congr`). -/
theorem ModelSatisfiesPCs_distinct {Ψ : FnCtx} {opInterp : Lambda.OpInterp simpTcInterp}
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} :
    ∀ (es : List (Imperative.PathConditionEntry Expression)) (Φ0 : FVarCtx)
      (h : PathEntriesWF Ψ Φ0 es),
      ProofObligation.ModelSatisfiesPCs opInterp fvarVal es Φ0 h →
      ∀ (l : String) (es' : List Expression.Expr),
        Imperative.PathConditionEntry.distinct l es' ∈ es →
        ∀ {Φt Ψt : _} (e0 : Expression.Expr), e0 ∈ es' →
          ∀ (hw : ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es', LExpr.HasSimpType Φt Ψt [] e τ),
          (distinctDenote opInterp fvarVal es' hw).Nodup := by
  intro es
  induction es with
  | nil => intro _ _ _ l es' hin _ _ _ _; simp at hin
  | cons entry rest ih =>
    intro Φ0 h hms l es' hin Φt Ψt e0 he0 hw
    simp only [ProofObligation.ModelSatisfiesPCs] at hms
    obtain ⟨hpc, hrest⟩ := hms
    rcases List.mem_cons.mp hin with rfl | hmem
    · simp only [ProofObligation.ModelSatisfiesPC] at hpc
      exact distinctDenote_Nodup_congr he0 (h.consInv.1).dstWitness hw hpc
    · exact ih (stepCtx Φ0 entry) h.consInv.2 hrest l es' hmem e0 he0 hw

/-- **Shared model-condition transfer** for both collect directions. From the raw obligation's
    model conditions (`Factory.ModelRespects` + `ModelSatisfiesPCs`) derive the collected context's
    three conditions (`DefConsistent`, asserts, distincts). Goal-polarity-independent. -/
theorem collectObligation_coreConditions
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    {uAT : Bool}
    (hcwf : CoreCtx.WF (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) d.obligation)
    (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hMR : Factory.ModelRespects F hsimp opInterp fvarVal)
    (hMS : ProofObligation.ModelSatisfiesPCs opInterp fvarVal d.assumptions.flatten [] hpwf.entriesWF) :
    CoreCtx.DefConsistent (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) d.obligation hcwf opInterp fvarVal
      ∧ CoreCtx.ModelSatisfiesAsserts (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) d.obligation hcwf opInterp fvarVal
      ∧ CoreCtx.ModelSatisfiesDistincts (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d) d.obligation hcwf opInterp fvarVal := by
  -- seen ⟹ nonPredefined (to feed `Factory.ModelRespects`, which ranges over `nonPredefined F tf`).
  have hexprNP : ∀ e ∈ obligationExprs d, ∀ nm ∈ exprFnRefs uAT e, isPredefinedOp nm = false := by
    intro e he nm hnm
    obtain ⟨Φ, τ, hty⟩ := obligationExprs_typed hpwf e he
    exact hasSimpType_exprFnRefs_notPredefined uAT hty nm hnm
  have hseenNP : ∀ nm ∈ (collectFuncsState uAT F tf d).seenFns, isPredefinedOp nm = false :=
    foldl_collectFuncs_seen_notPredefined hsimp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) hexprNP
  have f_nonPred : ∀ (f : LFunc CoreLParams), f ∈ F.toArray →
      f.name.name ∈ (collectFuncsState uAT F tf d).seenFns → f ∈ Factory.nonPredefined F tf := by
    intro f hf hfseen
    refine mem_nonPredefined.mpr ⟨Array.mem_toList_iff.mpr hf, hseenNP f.name.name hfseen, ?_⟩
    exact foldl_collectFuncs_seen_notDatatypeOp (obligationExprs d) _
      (fun nm h => absurd h (by simp)) f.name.name hfseen
  have hchunks := collectObligation_chunks (uAT := uAT) (F := F) (tf := tf) (karities := karities) d
  refine ⟨?_, ?_, ?_⟩
  · -- DefConsistent
    refine ⟨?_, ?_⟩
    · -- fnDefs half: transport `hMR`'s per-`f` define-fun equation to the reachable `d'`.
      intro d' hd' bvarVal
      obtain ⟨f, hf, hfseen, hrec, body, hbody, hname, hargs, hret, hbdy⟩ :=
        collectObligation_fnDefs_mem d d' hd'
      have htyeq : Lambda.BVarVal simpTcInterp simpTyVarVal d'.argTys
                 = Lambda.BVarVal simpTcInterp simpTyVarVal f.inputs.values := by rw [hargs]
      have hbvHEq : HEq bvarVal (cast htyeq bvarVal) := (cast_heq htyeq bvarVal).symm
      have hmr := hMR.1 f (f_nonPred f hf hfseen) body hrec hbody (cast htyeq bvarVal)
      apply eq_of_heq
      refine HEq.trans ?_ (HEq.trans (heq_of_eq hmr) ?_)
      · exact applyBVarVal_heq hargs hret (by rw [hname, hret, hargs]) hbvHEq
      · exact simpDenote_heq hargs.symm hbvHEq.symm hbdy.symm hret.symm
    · -- det-var half: from `hMS`'s det entry via the varDef↔entry correspondence.
      intro v hv
      have hv' : v ∈ (obligationBaseCtx d).varDefs := by rw [← hchunks.2.2]; exact hv
      rcases foldl_oblStep_varDef_entry d.assumptions.flatten {} v hv' with h0 | ⟨name, ty, hin, hnm, hmono⟩
      · simp at h0
      · rw [hnm]
        exact ModelSatisfiesPCs_det d.assumptions.flatten [] hpwf.entriesWF hMS
          name ty v.body hin v.ty hmono (hcwf.varDefsWF.mem_hasTypeA v hv)
  · -- ModelSatisfiesAsserts
    refine ⟨?_, ?_⟩
    · -- assumption half
      intro e he
      have he' : e ∈ (obligationBaseCtx d).assumptions := by rw [← hchunks.1]; exact he
      rcases (foldl_oblStep_entry d.assumptions.flatten {}).1 e he' with h0 | ⟨l, hain⟩
      · simp at h0
      · exact ModelSatisfiesPCs_assumption d.assumptions.flatten [] hpwf.entriesWF hMS l e hain _
    · -- fn-axiom half: every reachable axiom is some reachable `f`'s axiom.
      intro e he
      obtain ⟨f, hf, hfseen, hfe⟩ := collectObligation_fnAxioms_mem d e he
      exact hMR.2 f (f_nonPred f hf hfseen) e hfe
  · -- ModelSatisfiesDistincts
    intro es hes
    have hes' : es ∈ (obligationBaseCtx d).distincts := by rw [← hchunks.2.1]; exact hes
    rcases (foldl_oblStep_entry d.assumptions.flatten {}).2 es hes' with h0 | ⟨l, hdin⟩
    · simp at h0
    · by_cases hnil : es = []
      · subst hnil; simp [distinctDenote]
      · obtain ⟨e0, t, rfl⟩ := List.exists_cons_of_ne_nil hnil
        exact ModelSatisfiesPCs_distinct d.assumptions.flatten [] hpwf.entriesWF hMS
          l (e0 :: t) hdin e0 List.mem_cons_self (hcwf.distinctsWF (e0 :: t) hes).2

/-- **Collect validity.** If the collected `CoreCtx` is denotationally valid then so is the raw
    obligation: the obligation's model conditions (`Factory.ModelRespects` + `ModelSatisfiesPCs`)
    imply the collected context's (`DefConsistent`, asserts, distincts). -/
theorem collect_valid
    -- ── source side ──
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    -- ── correspondence (collecting: the `uAT`-configured `collectObligation`, whose `CoreCtx.WF` is `collect_WF`) ──
    {uAT : Bool}
    (hcvalid : CoreCtx.Valid (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d)
      d.obligation (collect_WF (uAT := uAT) hpwf hsimp).1) :
    ProofObligation.Valid F d hpwf hsimp := by
  intro divByZero modByZero opInterp hop fvarVal hMR hMS
  obtain ⟨hdef, hass, hdist⟩ :=
    collectObligation_coreConditions hpwf hsimp (collect_WF (uAT := uAT) hpwf hsimp).1
      divByZero modByZero opInterp hop fvarVal hMR hMS
  exact hcvalid divByZero modByZero opInterp hop fvarVal hdef hass hdist

/-- **Collect unsatisfiability.** The dual of `collect_valid`: if the collected `CoreCtx` is
    denotationally unsatisfiable then so is the raw obligation. -/
theorem collect_unsat
    -- ── source side ──
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    -- ── correspondence (collecting: the `uAT`-configured `collectObligation`, whose `CoreCtx.WF` is `collect_WF`) ──
    {uAT : Bool}
    (hcunsat : CoreCtx.Unsat (collectObligation uAT ⟨F, tf, karities, unmanagedFVars d⟩ d)
      d.obligation (collect_WF (uAT := uAT) hpwf hsimp).1) :
    ProofObligation.Unsat F d hpwf hsimp := by
  intro divByZero modByZero opInterp hop fvarVal hMR hMS
  obtain ⟨hdef, hass, hdist⟩ :=
    collectObligation_coreConditions hpwf hsimp (collect_WF (uAT := uAT) hpwf hsimp).1
      divByZero modByZero opInterp hop fvarVal hMR hMS
  exact hcunsat divByZero modByZero opInterp hop fvarVal hdef hass hdist

end Core.Refactor
