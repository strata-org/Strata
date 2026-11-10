/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.MonomorphizeFunctions
public import Strata.Languages.Core.Analysis.DeductiveVerificationProps
public import Strata.Languages.Core
public import Strata.Languages.Core.Analysis.FragmentFactory
public import Strata.DL.Lambda.LFuncEvalSound
import all Strata.Languages.Core
import all Strata.Languages.Core.PipelinePhase
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.LTyUnifyProps
import Strata.DL.Lambda.LTyProps
import Strata.Util.ListMapProps
import all Strata.DL.Lambda.LExprTraversal
import Strata.DL.Lambda.LExprTraversalProps
import Std.Data.HashMap.Lemmas
import all Strata.Transform.MonomorphizeFunctions
import all Strata.Util.Worklist
import all Init.Data.Queue
import all Strata.Transform.CoreTransform
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LFuncEvalSound
public import Strata.DL.Lambda.LExprRenameOps
public import Strata.Transform.MonomorphizeBasics
public import Strata.Transform.MonomorphizeWorklist
import all Strata.DL.Lambda.LExprRenameOps
import all Strata.Transform.MonomorphizeBasics
import all Strata.Transform.MonomorphizeWorklist

/-! # Monomorphization: what a successful run computes

The output of a successful `monomorphizeFunctions` run, described through its copies: each
function of the output and of the new factory is an instance of an input function.

## Key results

- `run_ok` — what a successful run computes, on a program without procedures.
- `MonoPre` — what the phase needs of its input.
- `newFn_source` — every new function is a copy of a function of the input or the factory.
- `passMono_runs` — the phase's run in the form the pipeline uses.
-/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling Strata.PtrCache

/-! ### The specialized copies -/

/-- A specialization `x.2` of `x.1` is a type instance, under its mangled name, of a function
    at `x.1`'s source. -/
public def IsCopyOf (p : Program) (F : Lambda.Factory CoreLParams)
    (x : FuncSpecialization × Function) : Prop :=
  ∃ f ∈ x.1.functionsAt p F,
    x.2 = monomorphizeFunction f ⟨mangledName x.1.name x.1.typeSubst.givenTypes, ()⟩ x.1.typeSubst

/-- The invariant of the worklist state: every specialization recorded for the program comes
    from the program, every one recorded for the factory from the factory, and each is a copy. -/
def CopiesInv (p : Program) (F : Lambda.Factory CoreLParams) (st : MonoWorklistState) : Prop :=
  (∀ x ∈ st.specializedFnsInProg, (∃ didx, x.1.source = .program didx) ∧ IsCopyOf p F x) ∧
  (∀ x ∈ st.specializedFnsInFactory, x.1.source = .factory ∧ IsCopyOf p F x)

/-- Recording the copy of a function at a specialization keeps every recorded specialization a
    copy from the right source. -/
theorem addSpecializedFunctions_inv (P : PolymorphicFuncDecls) (p : Program)
    (F : Lambda.Factory CoreLParams) (fs : FuncSpecialization) (f : Function)
    (hf : f ∈ fs.functionsAt p F) (st : MonoWorklistState) (hst : CopiesInv p F st) :
    CopiesInv p F ((addSpecializedFunctions P F fs f).run st).2 := by
  have hcopy : IsCopyOf p F (fs, monomorphizeFunction f
      (mangleFuncName st.cache fs.name fs.typeSubst.givenTypes).1 fs.typeSubst) :=
    ⟨f, hf, by rw [mangleFuncName_fst]⟩
  unfold addSpecializedFunctions
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, pure, StateT.pure]
  cases hsrc : fs.source with
  | program didx =>
    refine ⟨fun x hx => ?_, fun x hx => hst.2 x hx⟩
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hst.1 x hx
    · exact ⟨⟨didx, hsrc⟩, hcopy⟩
  | factory =>
    refine ⟨fun x hx => hst.1 x hx, fun x hx => ?_⟩
    rcases Array.mem_push.mp hx with hx | rfl
    · exact hst.2 x hx
    · exact ⟨hsrc, hcopy⟩

/-- Processing a specialization keeps every recorded specialization a copy from the right
    source. -/
theorem processFuncSpecialization_inv (P : PolymorphicFuncDecls) (p : Program)
    (F : Lambda.Factory CoreLParams) (fs : FuncSpecialization) (st : MonoWorklistState)
    (hst : CopiesInv p F st) :
    CopiesInv p F ((processFuncSpecialization P p F fs).run st).2 := by
  unfold processFuncSpecialization
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s heq
  exact foldlM_state_inv_of_eq (CopiesInv p F) heq
    (fun m hm b s hs => by
      have h := addSpecializedFunctions_inv P p F fs m hm s hs
      simp only [StateT.run] at h ⊢
      simp only [StateT.bind]
      generalize addSpecializedFunctions P F fs m s = r at h ⊢
      exact h) hst

/-- What `run` computes, without the monad. -/
def runSt (p : Program) (cap : Nat) (s : Transform.CoreTransformState) :
    Except Transform.Err Program × Transform.CoreTransformState :=
  if !namesUnmangled p then (.error (mangledNameError p), s)
  else match s.factory.toArray.find? (hasMonoDelim ·.name.name) with
  | some f => (.error (delimNameError f.name.name), s)
  | none =>
    let F := s.factory
    let polyfuncDecls := collectPolymorphicFuncDecls p F
    match (processTopDecls polyfuncDecls F p).run PtrCache.empty with
    | (ptd, cache) =>
    match ptd with
    | (p1, seedRefs) =>
    let factorySeedRefs : Array FuncSpecialization :=
      F.toArray.foldl (init := #[]) fun acc lfunc =>
        if lfunc.typeArgs.isEmpty then
          acc.appendList (collectFromFunction polyfuncDecls F lfunc.toFunc)
        else acc
    match (Strata.Worklist.run (seedRefs ++ factorySeedRefs.toList)
      (processFuncSpecialization polyfuncDecls p1 F) cap).run
        { MonoWorklistState.init with cache := cache } with
    | (finished, endState) =>
    if !finished then (.error (Strata.Message.fromString
      "MonomorphizeFunctions: too many specializations (non-uniform polymorphic \
       recursion is not supported)"), s)
    else
      match (updateFunctionsInProgram polyfuncDecls F p1 endState.specializedFnsInProg).run
          endState.cache with
      | (out, cache) =>
      match (updateFactory polyfuncDecls F endState.specializedFnsInFactory).run cache with
      | (factory', _) => (.ok out, { s with factory := factory' })

/-- `run` computes `runSt`. -/
theorem run_eq (p : Program) (cap : Nat) (s : Transform.CoreTransformState) :
    (MonomorphizeFunctions.run p cap).run.run s = runSt p cap s := by
  unfold MonomorphizeFunctions.run runSt
  cases namesUnmangled p
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      StateT.bind, pure, ExceptT.pure, StateT.pure, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, Functor.map, StateT.map, Core.Transform.getFactory,
      Core.Transform.setFactory, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
      MonadStateOf.modifyGet, throw, throwThe, MonadExceptOf.throw]
    cases hf : s.factory.toArray.find? (hasMonoDelim ·.name.name) with
    | some f => rfl
    | none =>
    dsimp only
    generalize processTopDecls (collectPolymorphicFuncDecls p s.factory) s.factory p
      PtrCache.empty = r
    obtain ⟨⟨p1, seeds⟩, c⟩ := r
    dsimp only
    generalize (Strata.Worklist.run (m := StateM MonoWorklistState) (α := FuncSpecialization)
      _ _ cap) _ = w
    obtain ⟨fin, st⟩ := w
    cases fin
    · rfl
    · rfl

/-- The specializations the pass seeds its worklist with from the factory: those of every
    monomorphic factory function's expressions. -/
def factorySeeds (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams) :
    List FuncSpecialization :=
  (F.toArray.foldl (init := (#[] : Array FuncSpecialization)) fun acc lfunc =>
    if lfunc.typeArgs.isEmpty then acc.appendList (collectFromFunction P F lfunc.toFunc)
    else acc).toList

/-- **What a successful run computes**, on a program without procedures, together with the
    worklist run it ends with. -/
theorem run_ok' {p : Program} {cap : Nat} {s s' : Transform.CoreTransformState} {p' : Program}
    (hnp : ∀ d ∈ p.decls, d.kind ≠ .proc)
    (h : (MonomorphizeFunctions.run p cap).run.run s = (.ok p', s')) :
    namesUnmangled p = true ∧
    ∃ st : MonoWorklistState,
      let P := collectPolymorphicFuncDecls p s.factory
      let g := monoRen P s.factory
      CopiesInv { decls := p.decls.map (topDecl g) } s.factory st ∧
      p'.decls = (p.decls.map (topDecl g)).zipIdx.flatMap
        (updDecl g (specsByFnOf st.specializedFnsInProg)) ∧
      s'.factory = Lambda.Factory.ofArray
        (keptOf P s.factory g ++ copiesOf s.factory g st.specializedFnsInFactory).toArray ∧
      ∃ c, (Strata.Worklist.run
        (((processTopDecls P s.factory p).run PtrCache.empty).1.2 ++ factorySeeds P s.factory)
        (processFuncSpecialization P { decls := p.decls.map (topDecl g) } s.factory) cap).run
          { MonoWorklistState.init with cache := c } = (true, st) := by
  rw [run_eq] at h
  unfold runSt at h
  cases hn : namesUnmangled p
  · simp only [hn, Bool.not_false, ↓reduceIte] at h
    exact absurd (congrArg Prod.fst h) (by simp)
  · simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run] at h
    cases hf : s.factory.toArray.find? (hasMonoDelim ·.name.name) with
    | some f => rw [hf] at h; exact absurd (congrArg Prod.fst h) (by simp)
    | none =>
    rw [hf] at h
    dsimp only at h
    refine ⟨rfl, ?_⟩
    have hdecls := processTopDecls_decls (collectPolymorphicFuncDecls p s.factory) s.factory p
      hnp PtrCache.empty
    simp only [StateT.run] at hdecls
    generalize hpt : processTopDecls (collectPolymorphicFuncDecls p s.factory) s.factory p
      PtrCache.empty = r at h hdecls
    obtain ⟨⟨p1, seeds⟩, c⟩ := r
    have hp1 : p1 = { decls := p.decls.map (topDecl (monoRen (collectPolymorphicFuncDecls p
        s.factory) s.factory)) } := by
      cases p1; simp only at hdecls; simp [hdecls]
    subst hp1
    dsimp only at h
    generalize hw : (Strata.Worklist.run (m := StateM MonoWorklistState) (α := FuncSpecialization)
      _ _ cap) _ = w at h
    have hinv : CopiesInv { decls := p.decls.map (topDecl (monoRen
        (collectPolymorphicFuncDecls p s.factory) s.factory)) } s.factory w.2 := by
      rw [← hw]
      exact worklist_run_inv _ _ (fun a st hst => processFuncSpecialization_inv _ _ _ a st hst)
        _ cap _ ⟨by simp [MonoWorklistState.init], by simp [MonoWorklistState.init]⟩
    obtain ⟨fin, st⟩ := w
    cases fin
    · exact absurd (congrArg Prod.fst h) (by simp)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨st, hinv, ?_, ?_, c, ?_⟩
      rotate_right
      · simp only [StateT.run] at hpt ⊢; rw [hpt]; exact hw
      · have hu := updateFunctionsInProgram_decls (collectPolymorphicFuncDecls p s.factory)
          s.factory { decls := p.decls.map (topDecl (monoRen (collectPolymorphicFuncDecls p
            s.factory) s.factory)) } st.specializedFnsInProg st.cache
        simp only [StateT.run] at hu
        generalize updateFunctionsInProgram _ _ _ _ st.cache = q at h hu
        obtain ⟨out, c2⟩ := q
        dsimp only at h
        split at h
        cases h
        exact hu
      · generalize updateFunctionsInProgram _ _ _ _ st.cache = q at h
        obtain ⟨out, c2⟩ := q
        have hf := updateFactory_run (collectPolymorphicFuncDecls p s.factory) s.factory
          st.specializedFnsInFactory c2
        simp only [StateT.run] at hf
        dsimp only at h
        split at h
        rename_i f' _ heq
        rw [heq] at hf
        cases h
        exact hf

/-- **What a successful run computes**, on a program without procedures. -/
theorem run_ok {p : Program} {cap : Nat} {s s' : Transform.CoreTransformState} {p' : Program}
    (hnp : ∀ d ∈ p.decls, d.kind ≠ .proc)
    (h : (MonomorphizeFunctions.run p cap).run.run s = (.ok p', s')) :
    namesUnmangled p = true ∧
    ∃ st : MonoWorklistState,
      let P := collectPolymorphicFuncDecls p s.factory
      let g := monoRen P s.factory
      CopiesInv { decls := p.decls.map (topDecl g) } s.factory st ∧
      p'.decls = (p.decls.map (topDecl g)).zipIdx.flatMap
        (updDecl g (specsByFnOf st.specializedFnsInProg)) ∧
      s'.factory = Lambda.Factory.ofArray
        (keptOf P s.factory g ++ copiesOf s.factory g st.specializedFnsInFactory).toArray := by
  obtain ⟨hn, st, h1, h2, h3, -⟩ := run_ok' hnp h
  exact ⟨hn, st, h1, h2, h3⟩

/-! ## Runtime factories as folds of `pushIfNew` -/

section RuntimeFactory

open Core.Specification.Analysis

/-- The functions a declaration contributes to a runtime factory. -/
@[expose] public def declFns : Decl → List (LFunc CoreLParams)
  | .func f _ => [f.toLFunc]
  | .recFuncBlock fs _ => fs.map (·.toLFunc)
  | .type (.data block) _ =>
    match Lambda.genBlockFactory (T := CoreLParams) block with
    | .ok fs => fs.toArray.toList
    | .error _ => []
  | _ => []

/-- Adding a declaration to a runtime factory is pushing, in order, the functions it
    contributes. -/
theorem addToRuntimeFactory_eq (F : Lambda.Factory CoreLParams) (d : Decl) :
    d.addToRuntimeFactory F = (declFns d).foldl Lambda.Factory.pushIfNew F := by
  cases d with
  | type t md =>
    cases t with
    | data block =>
      simp only [Decl.addToRuntimeFactory, declFns]
      split <;> rename_i heq <;> simp only [heq, Lambda.Factory.append, List.foldl_nil,
          Array.foldl_toList]
    | _ => rfl
  | func f md => rfl
  | recFuncBlock fs md =>
    simp [Decl.addToRuntimeFactory, Decl.addFunctionsToFactory, declFns, List.foldl_map]
  | _ => rfl

/-- A runtime factory is the base with the functions the declarations contribute pushed in
    order. -/
theorem runtimeFactoryOf_eq (F : Lambda.Factory CoreLParams) (decls : List Decl) :
    runtimeFactoryOf F decls = (decls.flatMap declFns).foldl Lambda.Factory.pushIfNew F := by
  induction decls generalizing F with
  | nil => rfl
  | cons d ds ih =>
    simp only [runtimeFactoryOf, List.foldl_cons, List.flatMap_cons, List.foldl_append] at ih ⊢
    rw [← addToRuntimeFactory_eq]
    exact ih _

/-- A function of a factory after `pushIfNew` of a list was in the factory or in the list. -/
theorem mem_foldl_pushIfNew {T : LExprParams} :
    ∀ (l : List (LFunc T)) (F : Lambda.Factory T) (f : LFunc T),
      f ∈ (l.foldl Lambda.Factory.pushIfNew F).toArray → f ∈ F.toArray ∨ f ∈ l
  | [], F, f, h => .inl h
  | g :: l, F, f, h => by
    rcases mem_foldl_pushIfNew l _ f h with h' | h'
    · unfold Lambda.Factory.pushIfNew at h'
      split at h'
      · exact .inl h'
      · simp only [Lambda.Factory.push, Array.mem_push] at h'
        rcases h' with h' | rfl
        · exact .inl h'
        · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h')

/-- `pushIfNew` keeps the function found under a name. -/
theorem getElem?_pushIfNew_of {T : LExprParams} {F : Lambda.Factory T} {g f : LFunc T}
    {x : String} (h : F[x]? = some f) : (F.pushIfNew g)[x]? = some f := by
  unfold Lambda.Factory.pushIfNew
  split
  · exact h
  · rename_i hnew
    rw [Lambda.Factory.push_mem_match]
    split
    · rename_i hx
      subst hx
      exact absurd (Lambda.Factory.getElem?_some_implies_mem h) hnew
    · exact h

/-- Pushing a list with `pushIfNew` keeps the function found under a name. -/
theorem getElem?_foldl_pushIfNew_of {T : LExprParams} :
    ∀ (l : List (LFunc T)) {F : Lambda.Factory T} {f : LFunc T} {x : String},
      F[x]? = some f → (l.foldl Lambda.Factory.pushIfNew F)[x]? = some f
  | [], _, _, _, h => h
  | _ :: l, _, _, _, h => getElem?_foldl_pushIfNew_of l (getElem?_pushIfNew_of h)

/-- Adding a declaration to the runtime factory keeps the function found under a name. -/
theorem getElem?_addToRuntimeFactory_of {F : Lambda.Factory CoreLParams} {n : String}
    {g : LFunc CoreLParams} (h : F[n]? = some g) (d : Decl) :
    (d.addToRuntimeFactory F)[n]? = some g := by
  rw [addToRuntimeFactory_eq]
  exact getElem?_foldl_pushIfNew_of _ h

end RuntimeFactory

/-! ## The functions of the new factory are instances -/

section Instances

/-- `g` renames every operator without `#` to a name that demangles back to it. -/
def RenOK (g : CoreIdent → Option LMonoTy → CoreIdent) : Prop :=
  ∀ o ty, '#' ∉ o.name.toList → demangleName (g o ty).name = o.name

/-- The renaming the pass applies demangles back to every operator name without `#`. -/
theorem monoRen_ok (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams) :
    RenOK (monoRen P F) := by
  intro o ty h
  unfold monoRen
  split
  · split
    · exact demangleName_mangledName h _
    · exact demangleName_of_not_hash h
  · exact demangleName_of_not_hash h

/-- `hasMonoDelim s` is false exactly when `s` has no `#`. -/
theorem not_hasMonoDelim_iff (s : String) : hasMonoDelim s = false ↔ '#' ∉ s.toList := by
  simp only [hasMonoDelim, monoDelim, List.any_eq_false]
  simp only [String.reduceToList, List.mem_cons, ↓Char.isValue, List.not_mem_nil, or_false,
      decide_eq_true_eq]
  exact ⟨fun h hm => h _ hm rfl, fun h x hx hxe => h (hxe ▸ hx)⟩

/-- No operator of `e` has `#` in its name. -/
@[expose] public def OpsUnmangled (e : Expression.Expr) : Prop := ∀ o ∈ e.getOps, '#' ∉
    o.name.toList

/-- No operator of `f`'s body or axioms, and not `f`'s name, has `#`. -/
@[expose] public def FnUnmangled (f : LFunc CoreLParams) : Prop :=
  '#' ∉ f.name.name.toList ∧ ∀ e ∈ f.body.toList ++ f.axioms, OpsUnmangled e

/-- The operator of an annotated operator node of an expression is among its operators. -/
theorem mem_getOps_of_opAnnots {T : LExprParamsT} :
    ∀ {e : LExpr T} {p}, p ∈ e.opAnnots → p.1 ∈ e.getOps := by
  intro e
  induction e with
  | op m o ty =>
    intro p hp
    cases ty <;> simp_all [LExpr.opAnnots, LExpr.getOps]
  | const | bvar | fvar => intro p hp; simp [LExpr.opAnnots] at hp
  | _ => intro p hp; simp_all [LExpr.opAnnots, LExpr.getOps] <;> grind

/-- Replacing annotations keeps an expression's operators. -/
theorem getOps_replaceUserProvidedType {T : LExprParamsT} (f : T.TypeType → T.TypeType) :
    ∀ e : LExpr T, (e.replaceUserProvidedType f).getOps = e.getOps := by
  intro e
  induction e <;> simp_all [LExpr.replaceUserProvidedType, LExpr.getOps]

/-- Applying a type substitution keeps an expression's operators. -/
theorem getOps_applyTypeSubst (S : Subst) (e : Expression.Expr) :
    (e.applyTypeSubst S).getOps = e.getOps := by
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
  exact getOps_replaceUserProvidedType _ e

/-- The empty type substitution leaves an expression unchanged. -/
theorem applyTypeSubst_nil (e : Expression.Expr) : e.applyTypeSubst [] = e := by
  simp [LExpr.applyTypeSubst, Subst.hasEmptyScopes]

/-- Renaming every operator to itself leaves an expression unchanged. -/
theorem renameOps_id {T : LExprParams} : ∀ e : LExpr T.mono, e.renameOps (fun o _ => o) = e := by
  intro e
  induction e <;> simp_all [LExpr.renameOps]

/-- Every annotated operator of a substituted expression whose operators have no `#` is renamed
    by an admissible renaming to a name that demangles to it. -/
private theorem ops_ok {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    {S : Subst} {e : Expression.Expr} (he : OpsUnmangled e) :
    ∀ p ∈ (e.applyTypeSubst S).opAnnots, demangleName (g p.1 (some p.2)).name = p.1.name := by
  intro p hp
  have hmem := mem_getOps_of_opAnnots hp
  rw [getOps_applyTypeSubst] at hmem
  exact hg _ _ (he _ hmem)

/-- A function with its operators renamed is an instance of itself. -/
theorem fnInstance_renFn {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    (lf : LFunc CoreLParams) (hu : FnUnmangled lf) :
    FnInstance lf { lf with toFunc := renFn g lf.toFunc } := by
  refine ⟨[], g, demangleName_of_not_hash hu.1, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [renFn, LMonoTy.subst_nil]
    induction lf.inputs <;> simp_all <;> rfl
  · simp [renFn, LMonoTy.subst_nil]
  · simp [renFn, applyTypeSubst_nil]
  · simp [renFn, applyTypeSubst_nil]
  · intro e he; exact ops_ok hg (hu.2 e he)
  · intro b _ h; rwa [applyTypeSubst_nil, LMonoTy.subst_nil] at h
  · intro a _ h; rwa [applyTypeSubst_nil] at h

/-- A function is an instance of itself. -/
theorem fnInstance_self (lf : LFunc CoreLParams) (hu : FnUnmangled lf) : FnInstance lf lf := by
  refine ⟨[], fun o _ => o, demangleName_of_not_hash hu.1, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [LMonoTy.subst_nil]
    induction lf.inputs <;> simp_all <;> rfl
  · simp [LMonoTy.subst_nil]
  · cases lf.body <;> simp [applyTypeSubst_nil, renameOps_id]
  · simp [applyTypeSubst_nil, renameOps_id]
  · intro e he p _; exact demangleName_of_not_hash (hu.2 e he p.1 (by
      have := mem_getOps_of_opAnnots ‹_›; rwa [getOps_applyTypeSubst] at this))
  · intro b _ h; rwa [applyTypeSubst_nil, LMonoTy.subst_nil] at h
  · intro a _ h; rwa [applyTypeSubst_nil] at h

/-- The copy of a function at an instantiation is an instance of the function, when the
    function's body and axioms are well typed. -/
theorem fnInstance_copy {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    (lf : LFunc CoreLParams) (hu : FnUnmangled lf) (ts : TypeArgsSubstitution)
    (hb : ∀ b, lf.body = some b → b.HasTypeA [] lf.output)
    (ha : ∀ a ∈ lf.axioms, a.HasTypeA [] .bool) :
    FnInstance lf { toFunc := renFn g (monomorphizeFunction lf.toFunc
      ⟨mangledName lf.name.name ts.givenTypes, ()⟩ ts), concreteEval := lf.concreteEval } := by
  refine ⟨ts.subst, g, demangleName_mangledName hu.1 _, ?_, rfl, ?_, ?_, rfl, ?_,
    fun b h _ => hb b h, fun a h _ => ha a h⟩
  · simp only [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst]; rfl
  · simp [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst, Option.map_map,
      Function.comp_def]
  · simp [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst, List.map_map,
      Function.comp_def]
  · intro e he; exact ops_ok hg (hu.2 e he)

end Instances

/-! ## Where the functions of the output come from -/

section Sources

/-- A copy grouped under a declaration index and a name is a recorded copy of the function of
    that name at that index. -/
theorem mem_specsByFnOf {specs : Array (FuncSpecialization × Function)} {j : Nat} {n : String}
    {x : FuncSpecialization × Function} (hx : x ∈ ((specsByFnOf specs).getD (j, n) #[]).toList) :
    x ∈ specs ∧ x.1.source = .program j ∧ x.1.name = n := by
  unfold specsByFnOf at hx
  rw [← Array.foldl_toList] at hx
  suffices h : ∀ (l : List (FuncSpecialization × Function))
      (m : Std.HashMap (Nat × String) (Array (FuncSpecialization × Function))),
      (∀ y ∈ (m.getD (j, n) #[]).toList, y ∈ specs ∧ y.1.source = .program j ∧ y.1.name = n) →
      (∀ y ∈ l, y ∈ specs) →
      x ∈ ((l.foldl (fun m x =>
        match x.fst.source with
        | .program didx => m.insert (didx, x.fst.name) ((m.getD (didx, x.fst.name) #[]).push
            (x.fst, x.snd))
        | .factory => m) m).getD (j, n) #[]).toList →
      x ∈ specs ∧ x.1.source = .program j ∧ x.1.name = n by
    exact h _ ∅ (fun y hy => by simp at hy) (fun y hy => by simpa using hy) hx
  intro l
  induction l with
  | nil => intro m hm _ hx; exact hm x hx
  | cons y l ih =>
    intro m hm hl hx
    refine ih _ ?_ (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hx
    intro z hz
    simp only at hz
    split at hz
    · rename_i didx hsrc
      rw [Std.HashMap.getD_insert] at hz
      split at hz
      · rename_i hk
        simp only [beq_iff_eq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hm z hz
        · exact ⟨hl _ List.mem_cons_self, hsrc, rfl⟩
      · exact hm z hz
    · exact hm z hz

/-- A function `updateFactory` keeps is a function of the original factory with operators
    renamed. -/
theorem mem_keptOf {P : PolymorphicFuncDecls} {F : Lambda.Factory CoreLParams}
    {g : CoreIdent → Option LMonoTy → CoreIdent} {f : LFunc CoreLParams} (h : f ∈ keptOf P F g) :
    ∃ lf ∈ F.toArray, f = { lf with toFunc := renFn g lf.toFunc } := by
  unfold keptOf at h
  rw [Array.mem_toList_iff] at h
  suffices hs : ∀ (l : List (LFunc CoreLParams)) (acc : Array (LFunc CoreLParams)),
      (∀ y ∈ acc, ∃ lf ∈ F.toArray, y = { lf with toFunc := renFn g lf.toFunc }) →
      (∀ y ∈ l, y ∈ F.toArray) →
      f ∈ l.foldl (fun (acc : Array (LFunc CoreLParams)) lfunc =>
        if lfunc.typeArgs.isEmpty ∨ !P.polyFactoryNames.contains lfunc.name.name then
          acc.push { lfunc with toFunc := renFn g lfunc.toFunc }
        else acc) acc →
      ∃ lf ∈ F.toArray, f = { lf with toFunc := renFn g lf.toFunc } by
    exact hs _ #[] (fun y hy => by simp at hy) (fun y hy => Array.mem_toList_iff.mp hy) h
  intro l
  induction l with
  | nil => intro acc hacc _ h; exact hacc f h
  | cons y l ih =>
    intro acc hacc hl h
    refine ih _ ?_ (fun z hz => hl z (List.mem_cons_of_mem _ hz)) h
    intro z hz
    dsimp only at hz
    split at hz
    · rcases Array.mem_push.mp hz with hz | rfl
      · exact hacc z hz
      · exact ⟨y, hl y List.mem_cons_self, rfl⟩
    · exact hacc z hz

end Sources

/-! ## What the phase needs of its input -/

section Pre

/-- The functions the factory `F` and the declarations `decls` contribute to a runtime
    factory, in order. -/
@[expose] public def contributed (F : Lambda.Factory CoreLParams) (decls : List Decl) : List
    (LFunc CoreLParams) :=
  F.toArray.toList ++ decls.flatMap declFns

/-- The functions a declaration declares: a function, or the members of a recursive block. -/
@[expose] public def progFns : Decl → List Function
  | .func f _ => [f]
  | .recFuncBlock fs _ => fs
  | _ => []

/-- `f`'s body and axioms are well typed. -/
@[expose] public def FnTyped (f : LFunc CoreLParams) : Prop :=
  (∀ b, f.body = some b → b.HasTypeA [] f.output) ∧ ∀ a ∈ f.axioms, a.HasTypeA [] .bool

/-- `f`'s concrete evaluator, if any, commutes with demangling operator names. -/
@[expose] public def EvalCommutesDemangle (f : LFunc CoreLParams) : Prop :=
  ∀ c, f.concreteEval = some c → ∀ md args res, c md args = some res →
    c md (args.map (·.renameOps demangleRen)) = some (res.renameOps demangleRen)

/-- The operator names the same-theory fragment's checks read: `Real.Mul` and `Real.Div` for
    linear real terms, `Real.Neg` for real literals,
    and the Boolean connectives for the polarity of string quantifiers. Renaming any of them
    could take a program out of the fragment, so the pass must leave them alone. -/
@[expose] public def fragmentOpNames : List String :=
  ["Real.Mul", "Real.Div", "Real.Neg", "Bool.Not", "Bool.And", "Bool.Or", "Bool.Implies"]

/-- Every operator of `e` naming a function of `R` with no type arguments is annotated with
    exactly that function's signature. An operator whose name `R` does not have is not
    constrained. -/
@[expose] public def MonoOpsAnnotated (R : Lambda.Factory CoreLParams) :
    Expression.Expr → Prop
  | .op _ name ty =>
    match R[name.name]? with
    | some fn => fn.typeArgs = [] →
        ty = some (Lambda.LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
    | none => True
  | .app _ f a => MonoOpsAnnotated R f ∧ MonoOpsAnnotated R a
  | .abs _ _ _ b => MonoOpsAnnotated R b
  | .ite _ c t f => MonoOpsAnnotated R c ∧ MonoOpsAnnotated R t ∧ MonoOpsAnnotated R f
  | .eq _ a b => MonoOpsAnnotated R a ∧ MonoOpsAnnotated R b
  | .quant _ _ _ _ tr b => MonoOpsAnnotated R tr ∧ MonoOpsAnnotated R b
  | _ => True

/-- Every axiom, lemma and function body of `p` is `MonoOpsAnnotated` over the runtime factory
    of `F` and `p`'s declarations. Function bodies are those of `Decl.func` declarations: the
    programs it is used on have no recursive function, so no `recFuncBlock`. -/
@[expose] public def ProgramOpsAnnotated (F : Lambda.Factory CoreLParams) (p : Program) : Prop :=
  (∀ a md, Decl.ax a md ∈ p.decls →
    MonoOpsAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) a.e) ∧
  (∀ l md, Decl.lemma l md ∈ p.decls →
    MonoOpsAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) l.e) ∧
  (∀ (f : Function) md (b : Expression.Expr), Decl.func f md ∈ p.decls → f.body = some b →
    MonoOpsAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) b)

/-- Every operator of `e` naming a function of `R` is annotated, with an instance of that
    function's signature: some substitution of the signature's type variables gives the
    annotation. Unlike `OpsConsistent`, which finds the substitution by unifying the annotation
    with the signature, this does not depend on how type variables are named, so an annotation
    that keeps a type variable of an enclosing declaration of the same name as one of the
    callee's still satisfies it. An operator whose name `R` does not have is not constrained. -/
@[expose] public def InstanceAnnotated (R : Lambda.Factory CoreLParams) :
    Expression.Expr → Prop
  | .op _ name ty =>
    match R[name.name]? with
    | some fn => ∃ t, ty = some t ∧ ∃ σ : Subst,
        t = LMonoTy.subst σ (Lambda.LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))
    | none => True
  | .app _ f a => InstanceAnnotated R f ∧ InstanceAnnotated R a
  | .abs _ _ _ b => InstanceAnnotated R b
  | .ite _ c t f => InstanceAnnotated R c ∧ InstanceAnnotated R t ∧ InstanceAnnotated R f
  | .eq _ a b => InstanceAnnotated R a ∧ InstanceAnnotated R b
  | .quant _ _ _ _ tr b => InstanceAnnotated R tr ∧ InstanceAnnotated R b
  | _ => True

/-- Every axiom, lemma and function body of `p` is `InstanceAnnotated` over the runtime factory
    of `F` and `p`'s declarations. -/
@[expose] public def ProgramInstanceAnnotated (F : Lambda.Factory CoreLParams) (p : Program) :
    Prop :=
  (∀ a md, Decl.ax a md ∈ p.decls →
    InstanceAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) a.e) ∧
  (∀ l md, Decl.lemma l md ∈ p.decls →
    InstanceAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) l.e) ∧
  (∀ (f : Function) md (b : Expression.Expr), Decl.func f md ∈ p.decls → f.body = some b →
    InstanceAnnotated (Core.Specification.Analysis.runtimeFactoryOf F p.decls) b)

/-- **What the phase needs of its input** (state `s`, program `p`):
    - `noProcs`: `p` declares no procedure;
    - `distinct`: the functions the state's factory and `p` contribute to a runtime factory
      have pairwise distinct names;
    - `unmangled`: none of them has a name, or an operator in its body or axioms, containing
      `#` (for `p`'s own names the phase checks this itself);
    - `typed`: the bodies and axioms of the state's functions and of `p`'s functions are well
      typed (a copy instantiates them);
    - `evals`: every concrete evaluator commutes with demangling;
    - `noConstr`: neither the state's factory nor `p` declares a constructor as a function;
    - `fragOps`: the state's factory has a monomorphic function of each name the same-theory
      fragment reads (`fragmentOpNames`), so the pass renames none of them;
    - the remaining fields are documented where they are declared. -/
public structure MonoPre (s : Transform.CoreTransformState) (p : Program) : Prop where
  noProcs : Core.Specification.Analysis.NoProcedures p
  distinct : ((contributed s.factory p.decls).map (·.name.name)).Nodup
  unmangled : ∀ f ∈ contributed s.factory p.decls, FnUnmangled f
  typed : (∀ f ∈ s.factory.toArray, FnTyped f) ∧ ∀ f ∈ p.decls.flatMap progFns, FnTyped f.toLFunc
  evals : ∀ f ∈ contributed s.factory p.decls, EvalCommutesDemangle f
  noConstr : (∀ f ∈ s.factory.toArray, f.isConstr = false) ∧
    ∀ f ∈ p.decls.flatMap progFns, f.isConstr = false
  fragOps : ∀ n ∈ fragmentOpNames, ∃ f ∈ s.factory.toArray, f.name.name = n ∧ f.typeArgs = []
  /-- The pass's instantiations are read off ground annotations. -/
  ground : groundInstantiationsB s.factory p = true
  /-- Every type parameter of a function occurs in its signature. -/
  sigTypeArgs : sigTypeArgsB s.factory p = true
  /-- The type constructors in operator annotations have plain names. -/
  plainAnnots : plainAnnotsB s.factory p = true
  /-- The state's factory keeps programs in the same-theory fragment when it evaluates. -/
  fragment : Core.Specification.Analysis.FragmentFactory s.factory
  /-- Each function of the state's factory has a sound evaluator, is well formed, has no
      body and is no constructor. -/
  baseEvalSound : ∀ fn ∈ s.factory.toArray,
    fn.EvalSound ∧ Lambda.LFuncWF fn ∧ fn.body = none ∧ fn.isConstr = Bool.false
  /-- Every datatype block is one datatype without recursive constructor arguments, in the
      shape `LDatatype.argsWF` checks. -/
  datatypesProvable : Core.Specification.Analysis.DatatypesProvable p = true
  /-- Every operator of an axiom, lemma or function body naming a monomorphic function of the
      runtime factory is annotated with exactly its signature. -/
  monoOpsAnnotated : ProgramOpsAnnotated s.factory p

/-- The functions contributed before a declaration are a sublist of those contributed by all of
    them. -/
theorem contributed_take_sublist (F : Lambda.Factory CoreLParams) (decls : List Decl) (i : Nat) :
    List.Sublist (contributed F (decls.take i)) (contributed F decls) := by
  unfold contributed
  refine List.Sublist.append_left ?_ _
  conv => rhs; rw [← List.take_append_drop i decls]
  rw [List.flatMap_append]
  exact List.sublist_append_left _ _

/-- A function a factory and declarations contribute, with names all distinct, is found in
    the runtime factory under its name. -/
theorem getElem?_runtimeFactoryOf_of_contributed {F : Lambda.Factory CoreLParams}
    {decls : List Decl} (hd : ((contributed F decls).map (·.name.name)).Nodup)
    {f : LFunc CoreLParams} (hf : f ∈ contributed F decls) :
    (Core.Specification.Analysis.runtimeFactoryOf F decls)[f.name.name]? = some f := by
  rw [runtimeFactoryOf_eq]
  unfold contributed at hd hf
  rw [List.map_append, List.nodup_append] at hd
  rcases List.mem_append.mp hf with hf | hf
  · exact getElem?_foldl_pushIfNew_of _ (Lambda.Factory.getElem?_of_mem_toArray F f
      (Array.mem_toList_iff.mp hf))
  · refine Lambda.Factory.get?_foldl_pushIfNew_of_mem f _ F hf ?_ hd.2.1
    intro hmem
    rw [Lambda.Factory.mem_iff_mem_names, ← Array.mem_toList_iff, Array.toList_map] at hmem
    exact hd.2.2 _ hmem _ (List.mem_map_of_mem hf) rfl

/-- Every function of a runtime factory is one the base or the declarations contribute. -/
theorem mem_contributed_of_runtimeFactoryOf {F : Lambda.Factory CoreLParams} {decls : List Decl}
    {f : LFunc CoreLParams}
    (hf : f ∈ (Core.Specification.Analysis.runtimeFactoryOf F decls).toArray) :
    f ∈ contributed F decls := by
  rw [runtimeFactoryOf_eq] at hf
  rcases mem_foldl_pushIfNew _ _ _ hf with h | h
  · exact List.mem_append_left _ (Array.mem_toList_iff.mpr h)
  · exact List.mem_append_right _ h

end Pre

/-! ## Copies, case by case -/

section CopyCases

/-- A recorded copy from a function declaration is that function instantiated and renamed. -/
theorem copy_func {p : Program} {F : Lambda.Factory CoreLParams} {x : FuncSpecialization × Function}
    {j : Nat} {f : Function} {md} (hsrc : x.1.source = .program j) (hc : IsCopyOf p F x)
    (hd : p.decls[j]? = some (.func f md)) :
    x.2 = monomorphizeFunction f ⟨mangledName x.1.name x.1.typeSubst.givenTypes, ()⟩ x.1.typeSubst
        := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc, getElem!_def, hd, List.mem_singleton] at hf0
  rw [h, hf0]

/-- A recorded copy from a recursive block is a member of the block, of the copy's base name,
    instantiated and renamed. -/
theorem copy_rec {p : Program} {F : Lambda.Factory CoreLParams} {x : FuncSpecialization × Function}
    {j : Nat} {ms : List Function} {md} (hsrc : x.1.source = .program j) (hc : IsCopyOf p F x)
    (hd : p.decls[j]? = some (.recFuncBlock ms md)) :
    ∃ f0 ∈ ms, f0.name.name = x.1.name ∧
      x.2 = monomorphizeFunction f0 ⟨mangledName x.1.name x.1.typeSubst.givenTypes, ()⟩
          x.1.typeSubst := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc, getElem!_def, hd, List.mem_filter,
    beq_iff_eq] at hf0
  exact ⟨f0, hf0.1, hf0.2, h⟩

/-- A recorded copy from the factory is the factory's function of the copy's base name,
    instantiated and renamed. -/
theorem copy_factory {p : Program} {F : Lambda.Factory CoreLParams}
    {x : FuncSpecialization × Function} (hsrc : x.1.source = .factory) (hc : IsCopyOf p F x) :
    ∃ lf, F[x.1.name]? = some lf ∧ lf.name.name = x.1.name ∧
      x.2 = monomorphizeFunction lf.toFunc ⟨mangledName x.1.name x.1.typeSubst.givenTypes, ()⟩
        x.1.typeSubst := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc] at hf0
  split at hf0
  · rename_i lf hlf
    simp only [List.mem_singleton] at hf0
    exact ⟨lf, hlf, Lambda.Factory.getElem?_name hlf, by rw [h, hf0]⟩
  · simp at hf0

/-- An indexed element among the first `i` of a list has an index below `i` and is the list's
    element at that index. -/
theorem mem_take_zipIdx {α : Type} {l : List α} {i : Nat} {x : α × Nat}
    (h : x ∈ (l.zipIdx).take i) : x.2 < i ∧ l[x.2]? = some x.1 := by
  refine ⟨?_, List.mem_zipIdx_iff_getElem?.mp (List.mem_of_mem_take h)⟩
  obtain ⟨j, hj, hx⟩ := List.mem_take_iff_getElem.mp h
  rw [List.getElem_zipIdx] at hx
  rw [← hx]
  simp only [Nat.zero_add]
  exact Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)

/-- The element at an index below `i` is among the first `i` elements. -/
theorem mem_take_of_getElem? {α : Type} {l : List α} {i j : Nat} {d : α} (hj : j < i)
    (h : l[j]? = some d) : d ∈ l.take i := by
  apply List.mem_of_getElem? (i := j)
  rw [List.getElem?_take, ite_eq_left hj, h]

end CopyCases

/-! ## Every function of the new runtime factory is an instance of one of the old -/

section NewFns

/-- A function a declaration declares is among the program's declared functions. -/
theorem mem_progFns {decls : List Decl} {d : Decl} (hd : d ∈ decls) {f : Function}
    (hf : f ∈ progFns d) : f ∈ decls.flatMap progFns :=
  List.mem_flatMap.mpr ⟨d, hd, hf⟩

/-- A function a declaration before index `i` contributes is among those the declarations before
    `i` contribute. -/
theorem mem_declPart_take {decls : List Decl} {i j : Nat}
    {d : Decl} (hj : j < i) (hd : decls[j]? = some d) {f : LFunc CoreLParams}
    (hf : f ∈ declFns d) : f ∈ (decls.take i).flatMap declFns :=
  List.mem_flatMap.mpr ⟨d, mem_take_of_getElem? hj hd, hf⟩

/-- Every function of the new state's factory is an instance of a function of the old one, and
    the same constructor if it is a constructor. -/
theorem newFn_source_base {s : Transform.CoreTransformState} {p : Program} (hpre : MonoPre s p)
    {P : PolymorphicFuncDecls} {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    {st : MonoWorklistState}
    (hinv : CopiesInv { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hb : f' ∈ (Lambda.Factory.ofArray (keptOf P s.factory g ++ copiesOf s.factory g
          st.specializedFnsInFactory).toArray).toArray.toList) :
    ∃ lf ∈ s.factory.toArray.toList, FnInstance lf f' ∧ (f'.isConstr = true → f' = lf) := by
  have hsub := contributed_take_sublist s.factory p.decls i
  have hun : ∀ lf ∈ contributed s.factory (p.decls.take i), FnUnmangled lf :=
    fun lf h => hpre.unmangled lf (hsub.subset h)
  have hb' := Lambda.Factory.ofArray_mem (Array.mem_toList_iff.mp hb)
  rw [List.mem_toArray, List.mem_append] at hb'
  rcases hb' with hk | hc
  · obtain ⟨lf, hlf, rfl⟩ := mem_keptOf hk
    have hlf' : lf ∈ contributed s.factory (p.decls.take i) :=
      List.mem_append_left _ (Array.mem_toList_iff.mpr hlf)
    refine ⟨lf, Array.mem_toList_iff.mpr hlf, fnInstance_renFn hg lf (hun lf hlf'), fun hc => ?_⟩
    have hnc := hpre.noConstr.1 lf hlf
    simp only [renFn] at hc
    rw [hnc] at hc; cases hc
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hsrc, hcopy⟩ := hinv.2 x (Array.mem_toList_iff.mp hx)
    obtain ⟨lf, hlf, hname, hx2⟩ := copy_factory hsrc hcopy
    have hlfm : lf ∈ s.factory.toArray := Lambda.Factory.getElem?_is_some_implies_mem hlf
    have hlf' : lf ∈ contributed s.factory (p.decls.take i) :=
      List.mem_append_left _ (Array.mem_toList_iff.mpr hlfm)
    have hce : ((s.factory.get? x.1.name).bind (·.concreteEval)) = lf.concreteEval := by
      change (s.factory[x.1.name]?.bind (·.concreteEval)) = _
      rw [hlf]; rfl
    rw [hce, hx2, ← hname]
    refine ⟨lf, Array.mem_toList_iff.mpr hlfm, fnInstance_copy hg lf (hun lf hlf') _ (hpre.typed.1
        lf hlfm).1
      (hpre.typed.1 lf hlfm).2, fun hc => ?_⟩
    have hnc := hpre.noConstr.1 lf hlfm
    simp only [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst] at hc
    rw [hnc] at hc; cases hc

/-- Every function the output's declarations before index `i` contribute is an instance of one
    the input's declarations before `i` contribute, and the same constructor if it is a
    constructor. -/
theorem newFn_source_decls {s : Transform.CoreTransformState} {p : Program} (hpre : MonoPre s p)
    {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    {st : MonoWorklistState}
    (hinv : CopiesInv { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hd : f' ∈ (((p.decls.map (topDecl g)).zipIdx.take i).flatMap
          (updDecl g (specsByFnOf st.specializedFnsInProg))).flatMap declFns) :
    ∃ lf ∈ (p.decls.take i).flatMap declFns, FnInstance lf f' ∧
      (f'.isConstr = true → f' = lf) := by
  have hsub := contributed_take_sublist s.factory p.decls i
  have hun : ∀ lf ∈ contributed s.factory (p.decls.take i), FnUnmangled lf :=
    fun lf h => hpre.unmangled lf (hsub.subset h)
  obtain ⟨d', hd', hf'd⟩ := List.mem_flatMap.mp hd
  obtain ⟨⟨dT, j⟩, hx, hd'u⟩ := List.mem_flatMap.mp hd'
  obtain ⟨hj, hdT⟩ := mem_take_zipIdx hx
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hdT
  obtain ⟨d0, hd0, rfl⟩ := hdT
  have hd0m : d0 ∈ p.decls := List.mem_of_getElem? hd0
  have hp1 : ({ decls := p.decls.map (topDecl g) } : Program).decls[j]? = some (topDecl g d0) := by
    simp [hd0]
  cases d0 with
  | func f md =>
    have hlf : f.toLFunc ∈ (p.decls.take i).flatMap declFns :=
      mem_declPart_take hj hd0 (by simp [declFns])
    have hfp : f ∈ p.decls.flatMap progFns := mem_progFns hd0m (by simp [progFns])
    have hnc := hpre.noConstr.2 f hfp
    simp only [topDecl, updDecl] at hd'u hp1
    split at hd'u
    · simp only [List.mem_singleton] at hd'u
      subst hd'u
      simp only [declFns, List.mem_singleton] at hf'd
      subst hf'd
      refine ⟨f.toLFunc, hlf, fnInstance_renFn hg f.toLFunc (hun _ (List.mem_append_right _ hlf)),
          fun hc => ?_⟩
      simp [renFn, LFuncDefined.toLFunc, hnc] at hc
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd'u
      obtain ⟨hyS, hysrc, hyname⟩ := mem_specsByFnOf hy
      obtain ⟨-, hcopy⟩ := hinv.1 y hyS
      have hy2 := copy_func hysrc hcopy hp1
      simp only [declFns, List.mem_singleton] at hf'd
      subst hf'd
      rw [hy2, hyname]
      refine ⟨f.toLFunc, hlf, fnInstance_copy hg f.toLFunc (hun _ (List.mem_append_right _ hlf)) _
        (hpre.typed.2 f hfp).1 (hpre.typed.2 f hfp).2, fun hc => ?_⟩
      simp [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst, LFuncDefined.toLFunc,
        hnc] at hc
  | recFuncBlock fs md =>
    simp only [topDecl, updDecl] at hd'u hp1
    split at hd'u
    · simp at hd'u
    · simp only [List.mem_singleton] at hd'u
      subst hd'u
      simp only [declFns, List.mem_map] at hf'd
      obtain ⟨m, hm, rfl⟩ := hf'd
      obtain ⟨f, hf, hmf⟩ := List.mem_flatMap.mp hm
      have mk : ∀ f0 ∈ fs, f0.toLFunc ∈ (p.decls.take i).flatMap declFns ∧
          f0 ∈ p.decls.flatMap progFns := fun f0 h0 =>
        ⟨mem_declPart_take hj hd0 (by simp only [declFns, List.mem_map]; exact ⟨f0, h0, rfl⟩),
         mem_progFns hd0m (by simpa [progFns] using h0)⟩
      split at hmf
      · simp only [List.mem_singleton] at hmf
        subst hmf
        obtain ⟨hlf, hfp⟩ := mk f hf
        refine ⟨f.toLFunc, hlf, fnInstance_renFn hg f.toLFunc (hun _ (List.mem_append_right _
            hlf)), fun hc => ?_⟩
        simp [renFn, LFuncDefined.toLFunc, hpre.noConstr.2 f hfp] at hc
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmf
        obtain ⟨hyS, hysrc, -⟩ := mem_specsByFnOf hy
        obtain ⟨-, hcopy⟩ := hinv.1 y hyS
        obtain ⟨f0, hf0, hname, hy2⟩ := copy_rec hysrc hcopy hp1
        obtain ⟨hlf, hfp⟩ := mk f0 hf0
        rw [hy2, ← hname]
        refine ⟨f0.toLFunc, hlf, fnInstance_copy hg f0.toLFunc (hun _ (List.mem_append_right _
            hlf)) _
          (hpre.typed.2 f0 hfp).1 (hpre.typed.2 f0 hfp).2, fun hc => ?_⟩
        simp [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst,
          LFuncDefined.toLFunc, hpre.noConstr.2 f0 hfp] at hc
  | type t md =>
    simp only [topDecl, updDecl, List.mem_singleton] at hd'u
    subst hd'u
    have hlf : f' ∈ (p.decls.take i).flatMap declFns := mem_declPart_take hj hd0 hf'd
    exact ⟨f', hlf, fnInstance_self f' (hun _ (List.mem_append_right _ hlf)), fun _ => rfl⟩
  | _ =>
    simp only [topDecl, updDecl, List.mem_singleton] at hd'u
    subst hd'u
    simp [declFns] at hf'd

/-- Every function of the output's runtime factory before index `i` is an instance of a function
    of the input's, and the same constructor if it is a constructor. -/
theorem newFn_source {s : Transform.CoreTransformState} {p : Program} (hpre : MonoPre s p)
    {P : PolymorphicFuncDecls} {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    {st : MonoWorklistState}
    (hinv : CopiesInv { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hf' : f' ∈ contributed
        (Lambda.Factory.ofArray (keptOf P s.factory g ++ copiesOf s.factory g
          st.specializedFnsInFactory).toArray)
        (((p.decls.map (topDecl g)).zipIdx.take i).flatMap
          (updDecl g (specsByFnOf st.specializedFnsInProg)))) :
    ∃ lf ∈ contributed s.factory (p.decls.take i), FnInstance lf f' ∧
      (f'.isConstr = true → f' = lf) := by
  rcases List.mem_append.mp hf' with hb | hd
  · obtain ⟨lf, hlf, h1, h2⟩ := newFn_source_base hpre hg hinv i hb
    exact ⟨lf, List.mem_append_left _ hlf, h1, h2⟩
  · obtain ⟨lf, hlf, h1, h2⟩ := newFn_source_decls hpre hg hinv i hd
    exact ⟨lf, List.mem_append_right _ hlf, h1, h2⟩

end NewFns

/-! ## Assembling the entry -/

section Assembly

/-- A function found by name belongs to the factory's array. -/
theorem getElem_mem_toArray {T : LExprParams} (F : Lambda.Factory T) (n : String) (hn : n ∈ F) :
    F[n]'hn ∈ F.toArray := by
  simp +instances only [Lambda.Factory.instGetElem?, Lambda.Factory.get]
  exact Array.getElem_mem _

/-- When the pass's name check accepts a program, no operator of a declaration's own expressions
    has `#`. -/
theorem opsUnmangled_of_namesUnmangled {p : Program} (h : namesUnmangled p = true) {d : Decl}
    (hd : d ∈ p.decls) {e : Expression.Expr} (he : e ∈ d.ownExprs) : OpsUnmangled e := by
  unfold namesUnmangled mangledNameIn? at h
  have hnone := List.find?_eq_none.mp (Option.isNone_iff_eq_none.mp h)
  intro o ho
  have hmem : o.name ∈ checkedNames p := by
    unfold checkedNames
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, ?_⟩)
    exact List.mem_flatMap.mpr ⟨e, List.mem_append_right _ he, List.mem_append_left _
        (List.mem_map_of_mem ho)⟩
  have := hnone _ hmem
  exact (not_hasMonoDelim_iff _).mp (by simpa using this)

/-- The image of the `i`-th element starts the flat map right after the images of the first `i`
    elements. -/
theorem flatMap_index {α β : Type} (L : List α) (U : α → List β) {i : Nat} {a : α} {b : β}
    (ha : L[i]? = some a) (hb : (U a).head? = some b) :
    (L.flatMap U)[((L.take i).flatMap U).length]? = some b ∧
      (L.flatMap U).take ((L.take i).flatMap U).length = (L.take i).flatMap U := by
  have hsplit : L = L.take i ++ a :: L.drop (i + 1) := by
    have h1 := List.take_append_drop i L
    have h2 : L.drop i = a :: L.drop (i + 1) := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ha
      rw [List.drop_eq_getElem_cons hlt, heq]
    rw [← h2]; exact h1.symm
  have hL : L.flatMap U = (L.take i).flatMap U ++ (U a ++ (L.drop (i + 1)).flatMap U) := by
    conv => lhs; rw [hsplit]
    simp [List.flatMap_append]
  rw [hL]
  refine ⟨?_, by simp⟩
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨c, cs, hc⟩ : ∃ c cs, U a = c :: cs := by
    cases h : U a with
    | nil => rw [h] at hb; cases hb
    | cons c cs => exact ⟨c, cs, rfl⟩
  rw [hc] at hb ⊢
  simp only [List.head?_cons, Option.some.injEq] at hb
  simp [hb]

/-- A run of the phase is a run of `MonomorphizeFunctions.run`. -/
theorem passMono_runs {s s' : Transform.CoreTransformState} {p p' : Program}
    (h : Strata.Core.passMonomorphizeFunctions.Runs s p s' p') :
    (MonomorphizeFunctions.run p).run.run s = (.ok p', s') := by
  obtain ⟨b, hb⟩ := h
  simp only [Strata.Core.passMonomorphizeFunctions, monomorphizeFunctionsPipelinePhase,
    modelPreservingPipelinePhase] at hb
  unfold monomorphizeFunctions at hb
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, pure, ExceptT.pure] at hb ⊢
  generalize (MonomorphizeFunctions.run p) s = r at hb ⊢
  obtain ⟨e, st⟩ := r
  cases e with
  | error => exact absurd (congrArg Prod.fst hb) (by simp [StateT.pure])
  | ok q =>
    simp only [StateT.pure] at hb
    cases hb
    rfl

end Assembly

end Core.MonomorphizeFunctions
