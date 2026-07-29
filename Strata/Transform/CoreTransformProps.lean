/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.Transform.CoreTransform
import all Strata.Transform.CoreTransform
import all Strata.Languages.Core.CoreGen
import all Strata.DL.Util.Maps

public section

/-! # Transformation-generic store/run helpers

Small, transformation-agnostic store/run inversion lemmas shared across the
structured-to-unstructured passes (`projectStore_undef_at`,
`stmts_cons_terminal_inv`).  They depend only on the base statement semantics, so
they sit below every pass-specific correctness proof. -/


namespace Imperative

variable {P : PureExpr}

/-! ## Store/run inversion helpers -/

/-- `projectStore` reverts to `none` on parent-undefined keys. -/
theorem projectStore_undef_at {P : PureExpr}
    {σ_parent σ_inner : SemanticStore P} {x : P.Ident}
    (h : σ_parent x = none) :
    projectStore σ_parent σ_inner x = none := by
  unfold projectStore
  simp [h]

/-- Split `.stmts (s :: rest) ρ ⟶* .terminal ρ'` into head and tail runs. -/
theorem stmts_cons_terminal_inv
    [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] [HasVarsPure P P.Expr]
    {extendFactory : ExtendFactory P}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendFactory (.stmts (s :: rest) ρ) (.terminal ρ')) :
    ∃ ρ_mid : Env P,
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) (.terminal ρ_mid) ∧
      StepStmtStar P (EvalCmd P) extendFactory (.stmts rest ρ_mid) (.terminal ρ') := by
  cases h with
  | step _ _ _ h1 hr1 => cases h1; exact seq_reaches_terminal P (EvalCmd P) extendFactory hr1

end Imperative

/-! # Core Transform — Theorems

Properties of the per-call-site type-variable freshening in
`Strata.Transform.CoreTransform`. Key results:

- `freshenTypeArgsSubst_fresh` — mechanism freshness: every type in the
  substitution's range is a fresh `<prefix>_<n>` variable, present in the output
  generator state and absent from the input's.
- `freshenTypeArgsSubst_disjoint` — cross-call-site disjointness: two successive
  call sites draw disjoint fresh ranges, which is what stops one inlined
  contract from unifying with another's.
- `freshenTypeArgsSubst_empty` — monomorphic callees (`typeArgs = []`) yield
  `Subst.empty` without touching the generator: an exact no-op.

The theorems are generic in the prefix string; call elimination instantiates it
with `freshTyVarPrefix` (`$__cety`, in `CallElim.lean`).

Key definitions the reader needs: `freshenTypeArgsSubst`, `genTyVarName(s)`
(in `CoreTransform.lean`), and `CoreGenState.WF` (in `CoreGen.lean`).

Proven against `StringGenState`'s counter monotonicity (`CoreGenState.WFMono`),
independent of the `CallElimCorrect` correctness proof; the whole-program
"emitted program type-checks" theorem is out of scope for this file.

Scope note: `freshenTypeArgsSubst_fresh` proves each fresh name carries the
reserved `<prefix>_<n>` shape, so the names are structurally in the prefix's
namespace. What remains convention (not lemma) is that the counter does not
ingest existing program identifiers, so a *user* who writes a literal
`<prefix>_<n>` type variable could still collide; safety there rests on the
`$__` reservation (see `freshTyVarPrefix` in `CallElim.lean`). Freshness and
disjointness across call sites — the property that actually prevents
cross-site unification — is fully proven here.
-/


namespace Core
namespace Transform

variable (prefixStr : String)

/-- `Map.values` is `map Prod.snd` (used to reason about the substitution
    range below; file-local — promote to a `Map` properties file if needed
    more widely). -/
private theorem map_values_eq_map_snd (m : Map α β) : m.values = m.map Prod.snd := by
  induction m with
  | nil => rfl
  | cons p m ih => cases p; simp [Map.values, ih]

/-- `genTyVarName` is `CoreGenState.gen` at the fresh type-var prefix, with the
    generated string reified back into the `CoreIdent`. -/
private theorem genTyVarName_gen (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ = (⟨f, ()⟩, γ') := by
  unfold genTyVarName at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  obtain ⟨hf, hγ⟩ := h
  simp only [CoreGenState.gen, StringGenState.gen]

/-- One type-var draw grows `generated` by exactly the fresh ident. -/
private theorem genTyVarName_generated (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    γ'.generated = (⟨f, ()⟩ : CoreIdent) :: γ.generated := by
  have hg := genTyVarName_gen prefixStr γ γ' f h
  simp [CoreGenState.gen] at hg; rw [← hg.2, ← hg.1]

/-- One type-var draw preserves generator well-formedness. -/
private theorem genTyVarName_wf (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (hwf : γ.WF) (h : genTyVarName prefixStr γ = (f, γ')) : γ'.WF :=
  CoreGenState.WFMono' hwf (genTyVarName_gen prefixStr γ γ' f h)

/-- A drawn type-var name has the `<prefix>_<n>` shape — witnessing that it
    lives in the prefix's namespace (stronger than `startsWith`). -/
private theorem genTyVarName_form (γ γ' : CoreGenState) (f : Lambda.TyIdentifier)
    (h : genTyVarName prefixStr γ = (f, γ')) :
    ∃ n : Nat, f = prefixStr ++ "_" ++ toString n := by
  refine ⟨(Counter.genCounter γ.cs.cs).1, ?_⟩
  unfold genTyVarName at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  have h1 : (CoreGenState.gen (⟨prefixStr, ()⟩ : CoreIdent) γ).fst.name = f :=
    congrArg Prod.fst h
  rw [← h1]; simp only [CoreGenState.gen, StringGenState.gen]

/-- Generating `n` type-var names grows `generated` by exactly those idents. -/
private theorem genTyVarNames_generated (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    genTyVarNames prefixStr n γ = (fs, γ') →
    γ'.generated = (fs.reverse.map (fun f => (⟨f, ()⟩ : CoreIdent))) ++ γ.generated := by
  induction n with
  | zero =>
    intro γ γ' fs h
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs hγ; subst hfs hγ; simp
  | succ k ih =>
    intro γ γ' fs h
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with hfs hγ; subst hfs hγ
        rw [ih γ1 γ2 fs' h2, genTyVarName_generated prefixStr γ γ1 f h1]
        simp [List.reverse_cons, List.map_append]

/-- Generating `n` type-var names preserves generator well-formedness. -/
private theorem genTyVarNames_wf (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    γ.WF → genTyVarNames prefixStr n γ = (fs, γ') → γ'.WF := by
  induction n with
  | zero =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs hγ; subst hγ; exact hwf
  | succ k ih =>
    intro γ γ' fs hwf h
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with _ hγ; subst hγ
        exact ih γ1 _ fs' (genTyVarName_wf prefixStr γ γ1 f hwf h1) h2

/-- Every generated type-var name lands in the output generator state. -/
private theorem genTyVarNames_mem (n : Nat) (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier)
    (h : genTyVarNames prefixStr n γ = (fs, γ')) :
    ∀ f ∈ fs, (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated := by
  intro f hf
  rw [genTyVarNames_generated prefixStr n γ γ' fs h]
  apply List.mem_append_left
  rw [List.map_reverse, List.mem_reverse]
  exact List.mem_map_of_mem hf

/-- Every generated type-var name is absent from the input generator state. -/
private theorem genTyVarNames_fresh (n : Nat) (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier)
    (hwf : γ.WF) (h : genTyVarNames prefixStr n γ = (fs, γ')) :
    ∀ f ∈ fs, (⟨f, ()⟩ : CoreIdent) ∉ γ.generated := by
  intro f hf
  have hnd : γ'.generated.Nodup := (genTyVarNames_wf prefixStr n γ γ' fs hwf h).2.2
  rw [genTyVarNames_generated prefixStr n γ γ' fs h] at hnd
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hin_pref : (⟨f, ()⟩ : CoreIdent) ∈ (fs.reverse.map (fun f => (⟨f, ()⟩ : CoreIdent))) := by
    rw [List.map_reverse, List.mem_reverse]; exact List.mem_map_of_mem hf
  intro hmem
  exact hdisj _ hin_pref _ hmem rfl

/-- Every generated type-var name has the `<prefix>_<n>` shape. -/
private theorem genTyVarNames_form (n : Nat) :
    ∀ (γ γ' : CoreGenState) (fs : List Lambda.TyIdentifier),
    genTyVarNames prefixStr n γ = (fs, γ') →
    ∀ f ∈ fs, ∃ k : Nat, f = prefixStr ++ "_" ++ toString k := by
  induction n with
  | zero =>
    intro γ γ' fs h f hf
    simp only [genTyVarNames, List.replicate, List.mapM_nil, pure, StateT.pure] at h
    injection h with hfs _; subst hfs; simp at hf
  | succ k ih =>
    intro γ γ' fs h f hf
    simp only [genTyVarNames, List.replicate, List.mapM_cons, bind, StateT.bind,
      pure, StateT.pure] at h
    split at h
    next f0 γ1 h1 =>
      split at h
      next fs' γ2 h2 =>
        injection h with hfs hγ; subst hfs
        rw [List.mem_cons] at hf
        cases hf with
        | inl hh => subst hh; exact genTyVarName_form prefixStr γ γ1 f h1
        | inr hh => exact ih γ1 γ2 fs' h2 f hh

/-- A monomorphic callee (`typeArgs = []`) yields the empty substitution and does
    not touch the generator — the exact no-op the docstring promises. -/
theorem freshenTypeArgsSubst_empty (γ : CoreGenState) :
    freshenTypeArgsSubst prefixStr [] γ = (Lambda.Subst.empty, γ) := by
  simp [freshenTypeArgsSubst, pure, StateT.pure]

/-- A polymorphic callee yields one substitution scope pairing each declared
    type variable with a name drawn from `genTyVarNames`. -/
private theorem freshenTypeArgsSubst_nonempty {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr typeArgs.length γ = (fresh, γ') ∧
      S = [(typeArgs.zip fresh).map (fun tf => (tf.1, Lambda.LMonoTy.ftvar tf.2))] := by
  unfold freshenTypeArgsSubst at h
  rw [if_neg (by simp [hne])] at h
  simp only [bind, StateT.bind, pure, StateT.pure] at h
  split at h
  next fresh γ1 hgen =>
    injection h with hS hγ
    exact ⟨fresh, by rw [← hγ]; exact hgen, hS.symm⟩

/-- Every type in the substitution's range is a fresh type variable produced by
    the generator for this call site. -/
private theorem freshenTypeArgsSubst_range {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hne : typeArgs ≠ []) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    ∃ fresh, genTyVarNames prefixStr typeArgs.length γ = (fresh, γ') ∧
      ∀ v ∈ Maps.values S, ∃ f ∈ fresh, v = Lambda.LMonoTy.ftvar f := by
  obtain ⟨fresh, hgen, hS⟩ := freshenTypeArgsSubst_nonempty prefixStr typeArgs γ γ' hne h
  refine ⟨fresh, hgen, ?_⟩
  intro v hv
  subst hS
  simp only [Maps.values, List.append_nil, map_values_eq_map_snd, List.map_map, List.mem_map] at hv
  obtain ⟨tf, htf, hveq⟩ := hv
  exact ⟨tf.2, (List.of_mem_zip htf).2, hveq.symm⟩

/-- Freshness: for a polymorphic callee, every type in the range of the
    per-call-site substitution is a fresh type variable that (a) carries the
    `<prefix>_<n>` shape (so it lies in the prefix's namespace),
    (b) is present in the output generator state, and (c) is absent from the input
    state — and the generator stays well-formed. This is the mechanism that keeps
    one call site's contract from unifying with another's. -/
theorem freshenTypeArgsSubst_fresh {S : Lambda.Subst}
    (typeArgs : List Lambda.TyIdentifier) (γ γ' : CoreGenState)
    (hwf : γ.WF) (h : freshenTypeArgsSubst prefixStr typeArgs γ = (S, γ')) :
    γ'.WF ∧
    ∀ v ∈ Maps.values S, ∃ f, v = Lambda.LMonoTy.ftvar f ∧
      (∃ n : Nat, f = prefixStr ++ "_" ++ toString n) ∧
      (⟨f, ()⟩ : CoreIdent) ∈ γ'.generated ∧ (⟨f, ()⟩ : CoreIdent) ∉ γ.generated := by
  by_cases hne : typeArgs = []
  · subst hne
    have := freshenTypeArgsSubst_empty prefixStr γ
    rw [h] at this; injection this with hS hγ; subst hS hγ
    exact ⟨hwf, by simp [Maps.values]⟩
  obtain ⟨fresh, hgen, hrange⟩ := freshenTypeArgsSubst_range prefixStr typeArgs γ γ' hne h
  refine ⟨genTyVarNames_wf prefixStr _ γ γ' fresh hwf hgen, ?_⟩
  intro v hv
  obtain ⟨f, hf_mem, hveq⟩ := hrange v hv
  exact ⟨f, hveq,
    genTyVarNames_form prefixStr _ γ γ' fresh hgen f hf_mem,
    genTyVarNames_mem prefixStr _ γ γ' fresh hgen f hf_mem,
    genTyVarNames_fresh prefixStr _ γ γ' fresh hwf hgen f hf_mem⟩

/-- Cross-call-site disjointness: the substitutions from two successive call
    sites (the second threaded through the first's output generator state) have
    disjoint fresh type-variable ranges. A fresh variable from site 2 is absent
    from `γ1.generated`, while every fresh variable from site 1 is present in it —
    so no name is shared, which is exactly what stops the two sites' contracts
    from unifying. -/
theorem freshenTypeArgsSubst_disjoint {S1 S2 : Lambda.Subst}
    (ta1 ta2 : List Lambda.TyIdentifier) (γ γ1 γ2 : CoreGenState)
    (hwf : γ.WF)
    (h1 : freshenTypeArgsSubst prefixStr ta1 γ = (S1, γ1))
    (h2 : freshenTypeArgsSubst prefixStr ta2 γ1 = (S2, γ2)) :
    ∀ v ∈ Maps.values S1, v ∉ Maps.values S2 := by
  have hwf1 : γ1.WF := (freshenTypeArgsSubst_fresh prefixStr ta1 γ γ1 hwf h1).1
  intro v hv1 hv2
  obtain ⟨g, hveq, _, hg_in1, _⟩ := (freshenTypeArgsSubst_fresh prefixStr ta1 γ γ1 hwf h1).2 v hv1
  obtain ⟨g', hveq', _, _, hg'_notin1⟩ := (freshenTypeArgsSubst_fresh prefixStr ta2 γ1 γ2 hwf1 h2).2 v hv2
  have hgg : g = g' := by rw [hveq] at hveq'; injection hveq'
  rw [hgg] at hg_in1
  exact hg'_notin1 hg_in1

end Transform
end Core

end -- public section
