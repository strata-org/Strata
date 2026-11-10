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
import all Strata.DL.Lambda.LExprRenameOps
import all Strata.Transform.MonomorphizeBasics

/-! # Monomorphization: the worklist

What the worklist driver of `monomorphizeFunctions` computes, read off its run: the invariants
it keeps, and that a drained run has processed every seed and every successor once.

## Key results

- `worklist_run_items_inv` — the driver keeps any invariant every processing step keeps.
- `worklist_run_dedup` — no two equal items are processed.
- `worklist_run_complete` — a drained run has processed every seed.
- `worklist_run_closed` — a drained run has processed every successor of every marked item.
-/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling Strata.PtrCache

/-! ### Running state computations whose results do not depend on the state -/

section StateRuns

variable {σ α β γ : Type}

/-- A `forIn` over a list, every step of which yields and changes a projection `π` of the
    accumulator by `step`, changes it by folding `step`, whatever the state. -/
private theorem forIn_run_proj (π : β → γ) (step : γ → α → γ) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, ∃ b' s', (f a b).run s = (ForInStep.yield b', s') ∧ π b' = step (π b) a) →
      ∀ b s, π ((forIn l b f).run s).1 = l.foldl step (π b)
  | [], _, _, b, s => rfl
  | a :: l, f, hf, b, s => by
    obtain ⟨b', s', hrun, hπ⟩ := hf a List.mem_cons_self b s
    have ih := forIn_run_proj π step l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s'
    simp only [StateT.run] at hrun
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind, hrun] at ih ⊢
    rw [List.foldl_cons, ← hπ]
    exact ih

/-- `mapM` with an action whose result does not depend on the state maps the results. -/
theorem mapM_run_fst (h : α → StateM σ β) (k : α → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ s, ∃ s', (h a).run s = (k a, s')) →
      ∀ s, ∃ s', (l.mapM h).run s = (l.map k, s')
  | [], _, s => ⟨s, rfl⟩
  | a :: l, hk, s => by
    obtain ⟨s1, h1⟩ := hk a List.mem_cons_self s
    obtain ⟨s2, h2⟩ := mapM_run_fst h k l (fun a ha => hk a (List.mem_cons_of_mem _ ha)) s1
    refine ⟨s2, ?_⟩
    simp only [StateT.run] at h1 h2
    simp only [List.mapM_cons, StateT.run, bind, StateT.bind, h1, h2, pure, StateT.pure,
      List.map_cons]

/-- `Option.mapM` with an action whose result does not depend on the state maps the
    result. -/
theorem optionMapM_run_fst (h : α → StateM σ β) (k : α → β) (o : Option α)
    (hk : ∀ a ∈ o, ∀ s, ∃ s', (h a).run s = (k a, s')) (s : σ) :
    ∃ s', (o.mapM h).run s = (o.map k, s') := by
  cases o with
  | none => exact ⟨s, rfl⟩
  | some a =>
    obtain ⟨s', h'⟩ := hk a rfl s
    refine ⟨s', ?_⟩
    simp only [StateT.run] at h'
    simp only [Option.mapM, StateT.run, Functor.map, StateT.map, h', Option.map_some]
    rfl

/-- A `forIn` over a list that ends with accumulator `a`, every step of which yields and
    changes a projection `π` of the accumulator by `step`, ends with `π a` the fold of `step`
    over the list from `π b`. -/
theorem forIn_run_proj_of_eq (π : β → γ) (step : γ → α → γ) {l : List α}
    {f : α → β → StateM σ (ForInStep β)} {b a : β} {s s' : σ}
    (heq : (forIn l b f : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, ∃ b' s', (f a b).run s = (ForInStep.yield b', s') ∧
      π b' = step (π b) a) :
    π a = l.foldl step (π b) := by
  have h := forIn_run_proj π step l f hf b s
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

end StateRuns

/-- What `processTopDecls` makes of a declaration other than a procedure. -/
public def topDecl (g : CoreIdent → Option LMonoTy → CoreIdent) : Decl → Decl
  | .ax a md => .ax { a with e := a.e.renameOps g } md
  | .lemma l md => .lemma { l with e := l.e.renameOps g } md
  | .distinct n es md => .distinct n (es.map (·.renameOps g)) md
  | d => d

/-- On a program without procedures, `processTopDecls` renames the operators of the axioms,
    lemmas and `distinct` declarations, and keeps the other declarations. -/
theorem processTopDecls_decls (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (p : Program) (hnp : ∀ d ∈ p.decls, d.kind ≠ .proc) (c : PtrCache mangleTy) :
    ((processTopDecls P F p).run c).1.1.decls = p.decls.map (topDecl (monoRen P F)) := by
  unfold processTopDecls
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  split
  rename_i a s heq
  rw [forIn_run_proj_of_eq Prod.fst (fun acc d => acc.push (topDecl (monoRen P F) d)) heq ?hf]
  · simp only [List.foldl_push_eq_append, Array.toList_append, List.nil_append]
  · intro d hd b s
    cases d with
    | proc => exact (hnp _ hd rfl).elim
    | ax a md =>
      obtain ⟨c', hc⟩ := mangleOpsInLExpr_run P F a.e s
      simp only [StateT.run] at hc
      simp only [StateT.run, StateT.bind, hc, StateT.pure, topDecl]
      exact ⟨_, _, rfl, rfl⟩
    | lemma l md =>
      obtain ⟨c', hc⟩ := mangleOpsInLExpr_run P F l.e s
      simp only [StateT.run] at hc
      simp only [StateT.run, StateT.bind, hc, StateT.pure, topDecl]
      exact ⟨_, _, rfl, rfl⟩
    | distinct n es md =>
      obtain ⟨c', hc⟩ := mapM_run_fst (mangleOpsInLExpr P F) (·.renameOps (monoRen P F)) es
        (fun e _ s => mangleOpsInLExpr_run P F e s) s
      simp only [StateT.run] at hc
      simp only [StateT.run, StateT.bind, hc, StateT.pure, topDecl]
      exact ⟨_, _, rfl, rfl⟩
    | func f md =>
      dsimp only
      split <;> exact ⟨_, _, rfl, rfl⟩
    | recFuncBlock fs md =>
      exact ⟨_, _, rfl, rfl⟩
    | type t md => exact ⟨_, _, rfl, rfl⟩

/-- What `mangleOpsInFunctionDecl` makes of a function: its expressions with operators
    renamed by `g`. -/
public def renFn (g : CoreIdent → Option LMonoTy → CoreIdent) (f : Function) : Function :=
  { f with
    body := f.body.map (·.renameOps g)
    axioms := f.axioms.map (·.renameOps g)
    preconditions := f.preconditions.map (fun pc => { pc with expr := pc.expr.renameOps g })
    measure := f.measure.map (·.renameOps g) }

/-- `mangleOpsInFunctionDecl` renames every operator of a function's expressions by `monoRen`,
    whatever the cache. -/
theorem mangleOpsInFunctionDecl_run (P : PolymorphicFuncDecls)
    (F : Lambda.Factory CoreLParams) (f : Function) (c : PtrCache mangleTy) :
    ∃ c', (mangleOpsInFunctionDecl P F f).run c = (renFn (monoRen P F) f, c') := by
  have hm : ∀ (e : Expression.Expr) (s : PtrCache mangleTy),
      ∃ s', (mangleOpsInLExpr P F e).run s = (e.renameOps (monoRen P F), s') :=
    fun e s => mangleOpsInLExpr_run P F e s
  obtain ⟨c1, h1⟩ := optionMapM_run_fst _ _ f.body (fun e _ => hm e) c
  obtain ⟨c2, h2⟩ := mapM_run_fst _ _ f.axioms (fun e _ => hm e) c1
  obtain ⟨c3, h3⟩ := mapM_run_fst
    (fun (pc : Strata.DL.Util.FuncPrecondition Expression.Expr ExpressionMetadata) => do
      let e ← mangleOpsInLExpr P F pc.expr
      pure { pc with expr := e })
    (fun pc => { pc with expr := pc.expr.renameOps (monoRen P F) }) f.preconditions
    (fun pc _ s => by
      obtain ⟨s', hs⟩ := mangleOpsInLExpr_run P F pc.expr s
      simp only [StateT.run] at hs
      exact ⟨s', by simp only [StateT.run, bind, StateT.bind, hs, pure, StateT.pure]⟩) c2
  obtain ⟨c4, h4⟩ := optionMapM_run_fst _ _ f.measure (fun e _ => hm e) c3
  refine ⟨c4, ?_⟩
  simp only [StateT.run] at h1 h2 h4
  simp only [StateT.run, bind, pure] at h3
  simp only [mangleOpsInFunctionDecl, StateT.run, bind, StateT.bind, h1, h2, h3, h4, pure,
    StateT.pure, renFn]

/-- The specialized copies `updateFunctionsInProgram` groups by declaration index and
    function name. -/
def specsByFnOf (specs : Array (FuncSpecialization × Function)) :
    Std.HashMap (Nat × String) (Array (FuncSpecialization × Function)) :=
  specs.foldl (fun m x =>
    match x.fst.source with
    | .program didx => m.insert (didx, x.fst.name) ((m.getD (didx, x.fst.name) #[]).push (x.fst,
        x.snd))
    | .factory => m) ∅

/-- What `updateFunctionsInProgram` makes of the declaration at an index. -/
def updDecl (g : CoreIdent → Option LMonoTy → CoreIdent)
    (m : Std.HashMap (Nat × String) (Array (FuncSpecialization × Function))) :
    Decl × Nat → List Decl
  | (.func f md, idx) =>
    if f.typeArgs.isEmpty then [.func (renFn g f) md]
    else (m.getD (idx, f.name.name) #[]).toList.map (fun x => .func (renFn g x.2) md)
  | (.recFuncBlock fs md, idx) =>
    let members := fs.flatMap fun f =>
      if f.typeArgs.isEmpty then [renFn g f]
      else (m.getD (idx, f.name.name) #[]).toList.map (fun x => renFn g x.2)
    if members.isEmpty then [] else [.recFuncBlock members md]
  | (d, _) => [d]

/-- An array `forIn` whose steps all yield pushes what the steps push. -/
private theorem forIn_array_run {σ α β : Type} (step : β → α → β) (xs : Array α)
    (f : α → β → StateM σ (ForInStep β))
    (hf : ∀ a ∈ xs.toList, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    (b : β) (s : σ) :
    ∃ s', (forIn xs b f).run s = (xs.toList.foldl step b, s') := by
  rw [← Array.forIn_toList]
  have h := forIn_run_proj id step xs.toList f
    (fun a ha b s => by obtain ⟨s', hs⟩ := hf a ha b s; exact ⟨_, s', hs, rfl⟩) b s
  exact ⟨_, Prod.ext h rfl⟩

/-- A list `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step`, whatever the state. -/
private theorem forIn_list_run {σ α β : Type} (step : β → α → β) (xs : List α)
    (f : α → β → StateM σ (ForInStep β))
    (hf : ∀ a ∈ xs, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    (b : β) (s : σ) :
    ∃ s', (forIn xs b f).run s = (xs.foldl step b, s') := by
  have h := forIn_run_proj id step xs f
    (fun a ha b s => by obtain ⟨s', hs⟩ := hf a ha b s; exact ⟨_, s', hs, rfl⟩) b s
  exact ⟨_, Prod.ext h rfl⟩

/-- An array `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step` over the array's elements, together with the state it ends in. -/
private theorem forIn_array_eq {σ α β : Type} (step : β → α → β) {xs : Array α}
    {f : α → β → StateM σ (ForInStep β)}
    (hf : ∀ a ∈ xs.toList, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    {b : β} {s : σ} :
    (forIn xs b f : StateM σ β) s = (xs.toList.foldl step b, ((forIn xs b f : StateM σ β) s).2) :=
        by
  obtain ⟨s', h⟩ := forIn_array_run step xs f hf b s
  simp only [StateT.run] at h
  rw [h]

/-- A list `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step`, together with the state it ends in. -/
private theorem forIn_list_eq {σ α β : Type} (step : β → α → β) {xs : List α}
    {f : α → β → StateM σ (ForInStep β)}
    (hf : ∀ a ∈ xs, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    {b : β} {s : σ} :
    (forIn xs b f : StateM σ β) s = (xs.foldl step b, ((forIn xs b f : StateM σ β) s).2) := by
  obtain ⟨s', h⟩ := forIn_list_run step xs f hf b s
  simp only [StateT.run] at h
  rw [h]

/-- Folding the appending of `h`'s results onto an array gives the array followed by `l.flatMap
    h`. -/
private theorem foldl_append_toArray {α β : Type} (h : α → List β) :
    ∀ (l : List α) (acc : Array β),
      (l.foldl (fun acc x => acc ++ (h x).toArray) acc).toList = acc.toList ++ l.flatMap h
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_append_toArray h l]
    simp [List.flatMap_cons]

/-- Folding the pushing of `h`'s results onto an array appends `l.map h` to it. -/
private theorem foldl_push_map {α β : Type} (h : α → β) :
    ∀ (l : List α) (acc : Array β), l.foldl (fun acc x => acc.push (h x)) acc = acc ++ (l.map
        h).toArray
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_push_map h l]
    simp

/-- `updateFunctionsInProgram` replaces each declaration by what `updDecl` makes of it. -/
theorem updateFunctionsInProgram_decls (P : PolymorphicFuncDecls)
    (F : Lambda.Factory CoreLParams) (p : Program) (specs : Array (FuncSpecialization × Function))
    (c : PtrCache mangleTy) :
    ((updateFunctionsInProgram P F p specs).run c).1.decls =
      p.decls.zipIdx.flatMap (updDecl (monoRen P F) (specsByFnOf specs)) := by
  unfold updateFunctionsInProgram
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  split
  rename_i a s heq
  have ha := forIn_run_proj_of_eq id
    (fun acc x => acc ++ (updDecl (monoRen P F) (specsByFnOf specs) x).toArray) heq ?hf
  · simp only [id] at ha
    rw [ha, foldl_append_toArray]
    simp
  · intro x hx b s
    obtain ⟨d, idx⟩ := x
    cases d with
    | func f md =>
      dsimp only
      split
      · rename_i hmono
        obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F f s
        simp only [StateT.run] at hc
        refine ⟨?b1, ?s1, ?run1, ?step1⟩
        case run1 => simp only [StateT.run, StateT.bind, hc]; rfl
        case step1 => simp [updDecl, hmono]
      · rename_i hpoly
        refine ⟨?b2, ?s2, ?run2, ?step2⟩
        case run2 =>
          simp only [StateT.run, StateT.bind]
          rw [forIn_array_eq (fun (acc : Array Decl) (x : FuncSpecialization × Function) =>
            acc.push (Decl.func (renFn (monoRen P F) x.2) md))]
          · rfl
          · intro x _ b s
            obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F x.2 s
            simp only [StateT.run] at hc
            exact ⟨c', by simp only [StateT.run, StateT.bind, hc]; rfl⟩
        case step2 =>
          simp only [id, foldl_push_map, updDecl, hpoly, specsByFnOf]
          rfl
    | recFuncBlock fs md =>
      let hl : Function → List Function := fun f =>
        if f.typeArgs.isEmpty then [renFn (monoRen P F) f]
        else ((specsByFnOf specs).getD (idx, f.name.name) #[]).toList.map
          (fun x => renFn (monoRen P F) x.2)
      have hmem : (fs.foldl (fun acc f => acc ++ (hl f).toArray) #[]).toList = fs.flatMap hl := by
        rw [foldl_append_toArray]; simp
      let members := fs.foldl (fun acc f => acc ++ (hl f).toArray) #[]
      refine ⟨if (!members.isEmpty) = true then b.push (.recFuncBlock members.toList md) else b,
        ?s3, ?run3, ?step3⟩
      case run3 =>
        dsimp only
        simp only [StateT.run, StateT.bind]
        rw [forIn_list_eq (fun (acc : Array Function) (f : Function) => acc ++ (hl f).toArray)]
        · by_cases hne : (!members.isEmpty) = true
          · rw [ite_eq_left hne]
            change (if (!members.isEmpty) = true then
              StateT.pure (ForInStep.yield (b.push (Decl.recFuncBlock members.toList md)))
              else StateT.pure (ForInStep.yield b)) _ = _
            rw [ite_eq_left hne]
            rfl
          · rw [ite_eq_right hne]
            change (if (!members.isEmpty) = true then
              StateT.pure (ForInStep.yield (b.push (Decl.recFuncBlock members.toList md)))
              else StateT.pure (ForInStep.yield b)) _ = _
            rw [ite_eq_right hne]
            rfl
        · intro f _ acc s
          split
          · rename_i hmono
            obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F f s
            simp only [StateT.run] at hc
            refine ⟨c', ?_⟩
            simp only [StateT.run, StateT.bind, hc]
            rw [show hl f = [renFn (monoRen P F) f] from ite_eq_left hmono]
            rfl
          · rename_i hpoly
            refine ⟨?s4, ?run4⟩
            case run4 =>
              simp only [StateT.run, StateT.bind]
              rw [forIn_array_eq (fun (acc : Array Function) (x : FuncSpecialization × Function) =>
                acc.push (renFn (monoRen P F) x.2))]
              · rw [show hl f = ((specsByFnOf specs).getD (idx, f.name.name) #[]).toList.map
                    (fun x => renFn (monoRen P F) x.2) from ite_eq_right hpoly, ← foldl_push_map]
                rfl
              · intro x _ b s
                obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F x.2 s
                simp only [StateT.run] at hc
                exact ⟨c', by simp only [StateT.run, StateT.bind, hc]; rfl⟩
      case step3 =>
        have hm2 : (fs.flatMap fun f => if f.typeArgs.isEmpty then [renFn (monoRen P F) f]
            else ((specsByFnOf specs).getD (idx, f.name.name) #[]).toList.map
              (fun x => renFn (monoRen P F) x.2)) = members.toList := hmem.symm
        simp only [id, updDecl]
        rw [hm2]
        generalize members = ms
        obtain ⟨l⟩ := ms
        cases l <;> simp
    | _ => exact ⟨_, _, rfl, by simp [updDecl]⟩

/-- The functions `updateFactory` keeps from the factory, with operators renamed. -/
public def keptOf (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (g : CoreIdent → Option LMonoTy → CoreIdent) : List (LFunc CoreLParams) :=
  (F.toArray.toList.foldl (fun (acc : Array (LFunc CoreLParams)) lfunc =>
    if lfunc.typeArgs.isEmpty ∨ !P.polyFactoryNames.contains lfunc.name.name then
      acc.push { lfunc with toFunc := renFn g lfunc.toFunc }
    else acc) #[]).toList

/-- The copies `updateFactory` adds to the factory, with operators renamed. -/
public def copiesOf (F : Lambda.Factory CoreLParams) (g : CoreIdent → Option LMonoTy → CoreIdent)
    (specs : Array (FuncSpecialization × Function)) : List (LFunc CoreLParams) :=
  specs.toList.map fun x =>
    { toFunc := renFn g x.2, concreteEval := (F.get? x.1.name).bind (·.concreteEval) }

/-- `updateFactory` builds the factory of the kept functions, with operators renamed, followed
    by the factory-sourced copies. -/
theorem updateFactory_run (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (specs : Array (FuncSpecialization × Function)) (c : PtrCache mangleTy) :
    ((updateFactory P F specs).run c).1 =
      Lambda.Factory.ofArray (keptOf P F (monoRen P F) ++ copiesOf F (monoRen P F) specs).toArray
          := by
  unfold updateFactory
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  rw [forIn_array_eq (fun (acc : Array (LFunc CoreLParams)) lfunc =>
    if lfunc.typeArgs.isEmpty ∨ !P.polyFactoryNames.contains lfunc.name.name then
      acc.push { lfunc with toFunc := renFn (monoRen P F) lfunc.toFunc }
    else acc)]
  · dsimp only
    rw [forIn_array_eq (fun (acc : Array (LFunc CoreLParams)) (x : FuncSpecialization × Function) =>
      acc.push { toFunc := renFn (monoRen P F) x.2,
                 concreteEval := (F.get? x.1.name).bind (·.concreteEval) })]
    · dsimp only
      rw [foldl_push_map]
      simp only [keptOf, copiesOf, Array.foldl_toList]
      congr 1
      apply Array.toList_inj.mp
      simp
    · intro x _ b s
      obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F x.2 s
      simp only [StateT.run] at hc
      exact ⟨c', by simp only [StateT.run, StateT.bind, hc]; rfl⟩
  · intro lf _ b s
    split
    · obtain ⟨c', hc⟩ := mangleOpsInFunctionDecl_run P F lf.toFunc s
      simp only [StateT.run] at hc
      exact ⟨c', by simp only [StateT.run, StateT.bind, hc]; rfl⟩
    · exact ⟨s, rfl⟩

/-! ### The worklist keeps an invariant of the state its steps keep -/

section WorklistInv

variable {σ α β : Type}

/-- A list `forIn` whose steps keep an invariant of the state keeps it. -/
private theorem forIn_state_inv (Inv : σ → Prop) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, Inv s → Inv ((f a b).run s).2) →
      ∀ b s, Inv s → Inv ((forIn l b f).run s).2
  | [], _, _, b, s, hs => hs
  | a :: l, f, hf, b, s, hs => by
    have h1 := hf a List.mem_cons_self b s hs
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f a b s = r at h1 ⊢
    obtain ⟨st, s'⟩ := r
    cases st with
    | done b' => exact h1
    | yield b' =>
      exact forIn_state_inv Inv l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

/-- A list `foldlM` whose steps keep an invariant of the state keeps it. -/
private theorem foldlM_state_inv (Inv : σ → Prop) :
    ∀ (l : List α) (f : β → α → StateM σ β),
      (∀ a ∈ l, ∀ b s, Inv s → Inv ((f b a).run s).2) →
      ∀ b s, Inv s → Inv ((l.foldlM f b).run s).2
  | [], _, _, b, s, hs => hs
  | a :: l, f, hf, b, s, hs => by
    have h1 := hf a List.mem_cons_self b s hs
    simp only [List.foldlM_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f b a s = r at h1 ⊢
    obtain ⟨b', s'⟩ := r
    exact foldlM_state_inv Inv l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

/-- A `forIn` loop ends in a state satisfying `Inv` when it starts in one and every step
    keeps `Inv`. -/
private theorem forIn_state_inv_of_eq (Inv : σ → Prop) {l : List α}
    {f : α → β → StateM σ (ForInStep β)} {b a : β} {s s' : σ}
    (heq : (forIn l b f : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, Inv s → Inv ((f a b).run s).2) (hs : Inv s) : Inv s' := by
  have h := forIn_state_inv Inv l f hf b s hs
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

/-- A monadic left fold ends in a state satisfying `Inv` when it starts in one and every
    step keeps `Inv`. -/
private theorem foldlM_state_inv_of_eq (Inv : σ → Prop) {l : List α}
    {f : β → α → StateM σ β} {b a : β} {s s' : σ}
    (heq : (l.foldlM f b : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, Inv s → Inv ((f b a).run s).2) (hs : Inv s) : Inv s' := by
  have h := foldlM_state_inv Inv l f hf b s hs
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

/-- One worklist iteration keeps an invariant of the state that every processing step keeps. -/
private theorem runOneIter_inv [BEq α] [Hashable α] (Inv : σ → Prop)
    (process : α → StateM σ (List α)) (hp : ∀ a s, Inv s → Inv ((process a).run s).2)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact hs
  · simp only [StateT.bind]
    have h1 := hp a s hs
    simp only [StateT.run] at h1
    generalize process _ s = r at h1 ⊢
    obtain ⟨news, s1⟩ := r
    show Inv ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
    refine foldlM_state_inv Inv news _ ?_ _ s1 h1
    intro a _ b s hs
    split <;> exact hs

/-- The worklist driver keeps an invariant of the state that every processing step keeps. -/
theorem worklist_run_inv [BEq α] [Hashable α] (Inv : σ → Prop) (process : α → StateM σ (List α))
    (hp : ∀ a s, Inv s → Inv ((process a).run s).2) (initial : List α) (cap : Nat) (s : σ)
    (hs : Inv s) : Inv ((Strata.Worklist.run initial process cap).run s).2 := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have h1 : Inv s' := forIn_state_inv_of_eq Inv heq
    (fun a _ b s hs => by split <;> exact hs) hs
  have hit : ∀ n st s, Inv s → Inv ((Strata.Worklist.runIterations process n st).run s).2 := by
    intro n
    induction n with
    | zero => intro st s hs; exact hs
    | succ n ih =>
      intro st s hs
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_inv Inv process hp st s hs
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      cases o with
      | none => exact h2
      | some st' => exact ih st' s2 h2
  exact hit cap _ s' h1

/-- Every item of a queue satisfies `Q`. -/
def QueueAll (Q : α → Prop) (q : Std.Queue α) : Prop := ∀ a ∈ q.eList ++ q.dList, Q a

/-- Dequeuing from a queue whose items satisfy `Q` gives an item satisfying `Q` and a queue whose
    items do. -/
private theorem QueueAll.dequeue? {Q : α → Prop} {q : Std.Queue α} (hq : QueueAll Q q) {a : α}
    {q' : Std.Queue α} (h : q.dequeue? = some (a, q')) : Q a ∧ QueueAll Q q' := by
  unfold Std.Queue.dequeue? at h
  split at h
  · rename_i d ds hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hq _ (by simp [hd]), fun b hb => hq b ?_⟩
    simp only [List.mem_append] at hb ⊢
    rcases hb with hb | hb
    · exact .inl hb
    · exact .inr (by rw [hd]; exact List.mem_cons_of_mem _ hb)
  · rename_i hd
    split at h
    · cases h
    · rename_i d ds hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmem : ∀ x ∈ d :: ds, x ∈ q.eList := fun x hx => by
        rw [← List.mem_reverse, hr]; exact hx
      refine ⟨hq _ (List.mem_append_left _ (hmem d List.mem_cons_self)), fun b hb => ?_⟩
      simp only [List.nil_append] at hb
      exact hq b (List.mem_append_left _ (hmem b (List.mem_cons_of_mem _ hb)))

/-- Enqueuing an item satisfying `Q` keeps every item of the queue satisfying `Q`. -/
private theorem QueueAll.enqueue {Q : α → Prop} {q : Std.Queue α} (hq : QueueAll Q q) {a : α}
    (ha : Q a) : QueueAll Q (q.enqueue a) := by
  intro b hb
  simp only [Std.Queue.enqueue, List.cons_append, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact ha
  · exact hq b hb

/-- A list `forIn` whose steps all yield and keep a property of the accumulator keeps it. -/
theorem forIn_acc_inv (P : β → Prop) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, P b → ∃ b', ((f a b).run s).1 = ForInStep.yield b' ∧ P b') →
      ∀ b s, P b → P ((forIn l b f).run s).1
  | [], _, _, b, s, hb => hb
  | a :: l, f, hf, b, s, hb => by
    obtain ⟨b', hy, hb'⟩ := hf a List.mem_cons_self b s hb
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind] at hy ⊢
    generalize f a b s = r at hy ⊢
    obtain ⟨st, s'⟩ := r
    simp only at hy
    subst hy
    exact forIn_acc_inv P l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' hb'

/-- A list `foldlM` whose steps keep a property of the accumulator keeps it. -/
theorem foldlM_acc_inv (P : β → Prop) :
    ∀ (l : List α) (f : β → α → StateM σ β),
      (∀ a ∈ l, ∀ b s, P b → P ((f b a).run s).1) →
      ∀ b s, P b → P ((l.foldlM f b).run s).1
  | [], _, _, b, s, hb => hb
  | a :: l, f, hf, b, s, hb => by
    have h1 := hf a List.mem_cons_self b s hb
    simp only [List.foldlM_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f b a s = r at h1 ⊢
    obtain ⟨b', s'⟩ := r
    exact foldlM_acc_inv P l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

/-- One worklist iteration keeps an invariant of the state and that every queued item satisfies
    `Q`, when processing an item satisfying `Q` keeps the invariant and discovers items
    satisfying `Q`. -/
private theorem runOneIter_items_inv [BEq α] [Hashable α] (Q : α → Prop) (Inv : σ → Prop)
    (process : α → StateM σ (List α))
    (hp : ∀ a s, Q a → Inv s → Inv ((process a).run s).2 ∧ ∀ b ∈ ((process a).run s).1, Q b)
    (st : Std.Queue α × Std.HashSet α) (hq : QueueAll Q st.1) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.runOneIter process st).run s).2 ∧
      ∀ st' ∈ ((Strata.Worklist.runOneIter process st).run s).1, QueueAll Q st'.1 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact ⟨hs, by simp [pure, StateT.pure]⟩
  · obtain ⟨hqa, hqp⟩ := hq.dequeue? hdq
    simp only [StateT.bind]
    have h1 := hp a s hqa hs
    simp only [StateT.run] at h1
    generalize process _ s = r at h1 ⊢
    obtain ⟨news, s1⟩ := r
    simp only at h1
    refine ⟨?_, ?_⟩
    · show Inv ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
      refine foldlM_state_inv Inv news _ ?_ _ s1 h1.1
      intro a _ b s hs
      split <;> exact hs
    · have hacc := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) => QueueAll Q x.1) news
        (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
          if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
          else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
        (fun b hb x s hx => by
          split
          · exact hx
          · exact hx.enqueue (h1.2 b hb)) (pending, st.snd) s1 hqp
      simp only [StateT.run] at hacc
      intro st' hst'
      have hst2 : st' ∈ some ((List.foldlM
          (fun (x : Std.Queue α × Std.HashSet α) b =>
            if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
            else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
          (pending, st.snd) news s1).fst) := hst'
      simp only [Option.mem_def, Option.some.injEq] at hst2
      subst hst2
      exact hacc

/-- **The worklist driver keeps an invariant of the state** that every processing step keeps
    on items satisfying `Q`, when the initial items satisfy `Q` and every item a step
    discovers does too. -/
theorem worklist_run_items_inv [BEq α] [Hashable α] (Q : α → Prop) (Inv : σ → Prop)
    (process : α → StateM σ (List α))
    (hp : ∀ a s, Q a → Inv s → Inv ((process a).run s).2 ∧ ∀ b ∈ ((process a).run s).1, Q b)
    (initial : List α) (hinit : ∀ a ∈ initial, Q a) (cap : Nat) (s : σ) (hs : Inv s) :
    Inv ((Strata.Worklist.run initial process cap).run s).2 := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have h1 : Inv s' := forIn_state_inv_of_eq Inv heq
    (fun a _ b s hs => by split <;> exact hs) hs
  have hq0 : QueueAll Q a.2 := by
    have hq := forIn_acc_inv (fun (x : Std.HashSet α × Std.Queue α) => QueueAll Q x.2) initial
      (fun (a : α) (x : Std.HashSet α × Std.Queue α) =>
        if (!x.fst.contains a) = true then
          (pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a x.snd)) : StateM σ _)
        else pure (ForInStep.yield (x.fst, x.snd)))
      (fun b hb x s hx => by
        split
        · exact ⟨_, rfl, hx.enqueue (hinit b hb)⟩
        · exact ⟨_, rfl, hx⟩) (∅, ∅) s (fun b hb => by
          simp only [List.mem_append] at hb
          rcases hb with hb | hb <;> cases hb)
    simp only [StateT.run] at hq
    rw [heq] at hq
    exact hq
  have hit : ∀ n st s, QueueAll Q st.1 → Inv s →
      Inv ((Strata.Worklist.runIterations process n st).run s).2 := by
    intro n
    induction n with
    | zero => intro st s _ hs; exact hs
    | succ n ih =>
      intro st s hq hs
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_items_inv Q Inv process hp st hq s hs
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      cases o with
      | none => exact h2.1
      | some st' => exact ih st' s2 (h2.2 st' rfl) h2.1
  exact hit cap _ s' hq0 h1

/-- The items of a queue, in the order `dequeue?` yields them. -/
def qlist (q : Std.Queue α) : List α := q.dList ++ q.eList.reverse

/-- Dequeuing yields the first item of the queue's list, and leaves the rest. -/
theorem qlist_dequeue? {q q' : Std.Queue α} {a : α} (h : q.dequeue? = some (a, q')) :
    qlist q = a :: qlist q' := by
  unfold Std.Queue.dequeue? at h
  split at h
  · rename_i d ds hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [qlist, hd]
  · rename_i hd
    split at h
    · cases h
    · rename_i d ds hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [qlist, hd, hr]

/-- Enqueuing appends to the queue's list. -/
theorem qlist_enqueue (q : Std.Queue α) (b : α) : qlist (q.enqueue b) = qlist q ++ [b] := by
  simp [qlist, Std.Queue.enqueue]

/-- What the worklist keeps for deduplication: the items processed, `P`, then those queued
    are pairwise distinct and all seen, and the items `proj` records are among those
    processed, in order. -/
def DedupInv [BEq α] [Hashable α] (proj : σ → List α) (P : List α) (Q : Std.Queue α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  (P ++ qlist Q).Pairwise (fun x y => (x == y) = false) ∧
    (∀ x ∈ P ++ qlist Q, S.contains x = true) ∧ (proj s).Sublist P

/-- Queuing an item that has not been seen, and marking it seen, keeps `DedupInv`. -/
private theorem DedupInv.enqueue [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {proj : σ → List α} {P : List α} {Q : Std.Queue α} {S : Std.HashSet α} {s : σ}
    (h : DedupInv proj P Q S s) {b : α} (hb : S.contains b = false) :
    DedupInv proj P (Q.enqueue b) (S.insert b) s := by
  obtain ⟨hp, hc, hs⟩ := h
  rw [DedupInv, qlist_enqueue, ← List.append_assoc]
  refine ⟨List.pairwise_append.mpr ⟨hp, by simp, ?_⟩, ?_, hs⟩
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    cases hxy : (x == y)
    · rfl
    · have := Std.HashSet.contains_congr (m := S) hxy
      rw [hc x hx, hb] at this; cases this
  · intro x hx
    rw [Std.HashSet.contains_insert]
    rcases List.mem_append.mp hx with hx | hx
    · rw [hc x hx]; simp
    · simp only [List.mem_singleton] at hx; subst hx; simp

/-- One worklist iteration either finds the queue empty and changes nothing, or keeps
    `DedupInv` with the item it processed added. -/
private theorem runOneIter_dedup [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (proj : σ → List α) (process : α → StateM σ (List α))
    (hp : ∀ a s, proj ((process a).run s).2 = proj s ∨ proj ((process a).run s).2 = proj s ++ [a])
    (st : Std.Queue α × Std.HashSet α) (s : σ) (P : List α) (h : DedupInv proj P st.1 st.2 s) :
    (((Strata.Worklist.runOneIter process st).run s).1 = none ∧
        ((Strata.Worklist.runOneIter process st).run s).2 = s) ∨
      ∃ a st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' ∧
        DedupInv proj (P ++ [a]) st'.1 st'.2 ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact .inl ⟨rfl, rfl⟩
  · simp only [StateT.bind]
    have hql := qlist_dequeue? hdq
    have h1 : DedupInv proj (P ++ [a]) pending st.2 s := by
      obtain ⟨hpw, hc, hsub⟩ := h
      rw [hql] at hpw hc
      exact ⟨by simpa using hpw, by simpa using hc, hsub.trans (List.sublist_append_left _ _)⟩
    have hpa := hp a s
    simp only [StateT.run] at hpa
    generalize process a s = r at hpa ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hpa
    have h2 : DedupInv proj (P ++ [a]) pending st.2 s1 := by
      refine ⟨h1.1, h1.2.1, ?_⟩
      rcases hpa with hpa | hpa
      · rw [hpa]; exact h1.2.2
      · rw [hpa]; exact h.2.2.append (List.Sublist.refl _)
    have hfold := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) =>
        DedupInv proj (P ++ [a]) x.1 x.2 s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x _ hx => by
        split
        · exact hx
        · rename_i hc
          exact hx.enqueue (by simpa using hc)) (pending, st.snd) s1 h2
    have hst := foldlM_state_inv (· = s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x s hs => by split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hfold hst
    refine .inr ⟨a, _, rfl, ?_⟩
    show DedupInv proj (P ++ [a]) _ _ ((List.foldlM _ (pending, st.snd) news : StateM σ _) s1).2
    rw [hst]
    exact hfold

/-- **The worklist processes no two equal items**, so it records no item twice in a state
    whose recorded list `proj` grows by at most the item each step processes. -/
theorem worklist_run_dedup [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (proj : σ → List α) (process : α → StateM σ (List α))
    (hp : ∀ a s, proj ((process a).run s).2 = proj s ∨ proj ((process a).run s).2 = proj s ++ [a])
    (initial : List α) (cap : Nat) (s : σ) (hs : proj s = []) :
    (proj ((Strata.Worklist.run initial process cap).run s).2).Pairwise
      (fun x y => (x == y) = false) := by
  unfold Strata.Worklist.run
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s' heq
  have hs' : s' = s := forIn_state_inv_of_eq (· = s) heq
    (fun a _ b s hs => by split <;> exact hs) rfl
  subst hs'
  have h0 : DedupInv proj [] a.2 a.1 s' := by
    have hd := forIn_acc_inv (fun (x : Std.HashSet α × Std.Queue α) => DedupInv proj [] x.2 x.1 s')
      initial
      (fun (a : α) (x : Std.HashSet α × Std.Queue α) =>
        if (!x.fst.contains a) = true then
          (pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a x.snd)) : StateM σ _)
        else pure (ForInStep.yield (x.fst, x.snd)))
      (fun b _ x _ hx => by
        split
        · rename_i hc
          exact ⟨_, rfl, hx.enqueue (by simpa using hc)⟩
        · exact ⟨_, rfl, hx⟩) (∅, ∅) s'
      ⟨List.Pairwise.nil, fun x hx => absurd hx List.not_mem_nil, by rw [hs]; exact .slnil⟩
    simp only [StateT.run] at hd
    rw [heq] at hd
    exact hd
  have hit : ∀ n (st : Std.Queue α × Std.HashSet α) s P, DedupInv proj P st.1 st.2 s →
      (proj ((Strata.Worklist.runIterations process n st).run s).2).Pairwise
        (fun x y => (x == y) = false) := by
    intro n
    induction n with
    | zero =>
      intro st s P h
      exact ((List.pairwise_append.mp h.1).1).sublist h.2.2
    | succ n ih =>
      intro st s P h
      unfold Strata.Worklist.runIterations
      simp only [StateT.run, bind, StateT.bind]
      have h2 := runOneIter_dedup proj process hp st s P h
      simp only [StateT.run] at h2
      generalize Strata.Worklist.runOneIter process st s = r at h2 ⊢
      obtain ⟨o, s2⟩ := r
      rcases h2 with ⟨ho, hs2⟩ | ⟨a, st', ho, hd⟩
      · simp only at ho hs2
        subst ho hs2
        exact ((List.pairwise_append.mp h.1).1).sublist h.2.2
      · simp only at ho hd
        subst ho
        exact ih st' s2 (P ++ [a]) hd
  exact hit cap (a.2, a.1) s' [] h0

/-! #### Completeness: a drained run has processed every seed -/

/-- A queue `dequeue?` finds empty has no items. -/
private theorem qlist_of_dequeue?_none {q : Std.Queue α} (h : q.dequeue? = none) : qlist q = [] :=
    by
  unfold Std.Queue.dequeue? at h
  split at h
  · cases h
  · rename_i hd
    split at h
    · rename_i hr
      simp [qlist, hd, List.reverse_eq_nil_iff.mp hr]
    · cases h

/-- An empty queue has no items. -/
private theorem qlist_of_isEmpty {q : Std.Queue α} (h : q.isEmpty = true) : qlist q = [] := by
  simp only [Std.Queue.isEmpty, Bool.and_eq_true, List.isEmpty_iff] at h
  simp [qlist, h.1, h.2]

/-- What completeness rests on: every item seen is done, or equal to one still queued. -/
def CompleteInv [BEq α] [Hashable α] (Done : σ → α → Prop) (Q : Std.Queue α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  ∀ x, S.contains x = true → Done s x ∨ ∃ y ∈ qlist Q, (x == y) = true

/-- Enqueuing an item and marking it seen keeps the completeness invariant: every seen item
    is still done or equal to one still queued. -/
private theorem CompleteInv.enqueue [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {Done : σ → α → Prop} {Q : Std.Queue α} {S : Std.HashSet α} {s : σ}
    (h : CompleteInv Done Q S s) (b : α) :
    CompleteInv Done (Q.enqueue b) (S.insert b) s := by
  intro x hx
  rw [Std.HashSet.contains_insert] at hx
  rw [qlist_enqueue]
  rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
  · exact .inr ⟨b, by simp, BEq.symm hx⟩
  · rcases h x hx with h | ⟨y, hy, hxy⟩
    · exact .inl h
    · exact .inr ⟨y, List.mem_append_left _ hy, hxy⟩

/-- One iteration either finds the queue empty, changing nothing, or keeps `CompleteInv`, when
    processing an item makes it done and keeps done items done. -/
private theorem runOneIter_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (h : CompleteInv Done st.1 st.2 s) :
    (((Strata.Worklist.runOneIter process st).run s).1 = none ∧
        ((Strata.Worklist.runOneIter process st).run s).2 = s ∧ qlist st.1 = []) ∨
      ∃ st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' ∧
        CompleteInv Done st'.1 st'.2 ((Strata.Worklist.runOneIter process st).run s).2 ∧
        ∀ x, st.2.contains x = true → st'.2.contains x = true := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · exact .inl ⟨rfl, rfl, qlist_of_dequeue?_none hdq⟩
  · simp only [StateT.bind]
    have hql := qlist_dequeue? hdq
    have hd := hdone a s
    have hm := hmono a s
    simp only [StateT.run] at hd hm
    generalize process a s = r at hd hm ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hd hm
    have h2 : CompleteInv Done pending st.2 s1 := by
      intro x hx
      rcases h x hx with hx | ⟨y, hy, hxy⟩
      · exact .inl (hm x hx)
      · rw [hql] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inl (hbeq s1 x y hxy hd)
        · exact .inr ⟨y, hy, hxy⟩
    have hfold := foldlM_acc_inv (fun (x : Std.Queue α × Std.HashSet α) =>
        CompleteInv Done x.1 x.2 s1 ∧ ∀ y, st.2.contains y = true → x.2.contains y = true) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x _ hx => by
        split
        · exact hx
        · refine ⟨hx.1.enqueue b, fun y hy => ?_⟩
          show (x.snd.insert b).contains y = true
          rw [Std.HashSet.contains_insert, hx.2 y hy, Bool.or_true]) (pending, st.snd) s1
      ⟨h2, fun _ hy => hy⟩
    have hst := foldlM_state_inv (· = s1) news
      (fun (x : Std.Queue α × Std.HashSet α) (b : α) =>
        if x.snd.contains b = true then (pure (x.fst, x.snd) : StateM σ _)
        else pure (Std.Queue.enqueue b x.fst, x.snd.insert b))
      (fun b _ x s hs => by split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hfold hst
    refine .inr ⟨_, rfl, ?_⟩
    dsimp only [pure, StateT.pure, bind, StateT.bind] at hfold hst ⊢
    generalize (List.foldlM _ (pending, st.snd) news : StateM σ _) s1 = r at hfold hst ⊢
    obtain ⟨⟨q', S'⟩, s'⟩ := r
    simp only at hfold hst ⊢
    subst hst
    exact hfold

/-- Iterating keeps `CompleteInv`, and when it reports the worklist drained, every seen item is
    done. -/
private theorem runIterations_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x) :
    ∀ n (st : Std.Queue α × Std.HashSet α) s, CompleteInv Done st.1 st.2 s →
      ((Strata.Worklist.runIterations process n st).run s).1 = true →
      ∀ x, st.2.contains x = true → Done ((Strata.Worklist.runIterations process n st).run s).2 x
  | 0, st, s, h, hfin, x, hx => by
    obtain ⟨pending, seen⟩ := st
    unfold Strata.Worklist.runIterations at hfin ⊢
    have hq := qlist_of_isEmpty hfin
    rcases h x hx with h | ⟨y, hy, -⟩
    · exact h
    · rw [hq] at hy; cases hy
  | n + 1, st, s, h, hfin, x, hx => by
    unfold Strata.Worklist.runIterations at hfin ⊢
    simp only [StateT.run, bind, StateT.bind] at hfin ⊢
    have h2 := runOneIter_complete Done process hmono hdone hbeq st s h
    simp only [StateT.run] at h2
    generalize Strata.Worklist.runOneIter process st s = r at h2 hfin ⊢
    obtain ⟨o, s2⟩ := r
    rcases h2 with ⟨ho, hs2, hq⟩ | ⟨st', ho, hd⟩
    · simp only at ho hs2
      subst ho hs2
      rcases h x hx with h | ⟨y, hy, -⟩
      · exact h
      · rw [hq] at hy; cases hy
    · simp only at ho hd
      subst ho
      exact runIterations_complete Done process hmono hdone hbeq n st' s2 hd.1 hfin x (hd.2 x hx)

/-- The body of `Strata.Worklist.run`'s seeding loop. -/
private abbrev seedStep [BEq α] [Hashable α] (a : α) (x : Std.HashSet α × Std.Queue α) :
    StateM σ (ForInStep (Std.HashSet α × Std.Queue α)) :=
  if (!x.fst.contains a) = true then pure (ForInStep.yield (x.fst.insert a, Std.Queue.enqueue a
      x.snd))
  else pure (ForInStep.yield (x.fst, x.snd))

/-- Seeding keeps `CompleteInv`, keeps what was seen, and sees every seed. -/
private theorem forIn_seed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (Done : σ → α →
    Prop)
    (s0 : σ) : ∀ (l : List α) (b : Std.HashSet α × Std.Queue α) (s : σ),
      CompleteInv Done b.2 b.1 s0 →
      CompleteInv Done ((forIn l b seedStep).run s).1.2 ((forIn l b seedStep).run s).1.1 s0 ∧
      (∀ x, b.1.contains x = true → ((forIn l b seedStep).run s).1.1.contains x = true) ∧
      (∀ a ∈ l, ((forIn l b seedStep).run s).1.1.contains a = true) ∧
      ((forIn l b seedStep).run s).2 = s
  | [], b, s, h => ⟨h, fun _ hx => hx, fun _ ha => absurd ha List.not_mem_nil, rfl⟩
  | a :: l, b, s, h => by
    have key : ∀ b' : Std.HashSet α × Std.Queue α, CompleteInv Done b'.2 b'.1 s0 →
        (∀ x, b.1.contains x = true → b'.1.contains x = true) → b'.1.contains a = true →
        ((forIn (a :: l) b seedStep).run s) = ((forIn l b' seedStep).run s) →
        CompleteInv Done ((forIn (a :: l) b seedStep).run s).1.2
            ((forIn (a :: l) b seedStep).run s).1.1 s0 ∧
          (∀ x, b.1.contains x = true →
            ((forIn (a :: l) b seedStep).run s).1.1.contains x = true) ∧
          (∀ a' ∈ a :: l, ((forIn (a :: l) b seedStep).run s).1.1.contains a' = true) ∧
          ((forIn (a :: l) b seedStep).run s).2 = s := by
      intro b' hb' hsub ha heq
      rw [heq]
      obtain ⟨h1, h2, h3, h4⟩ := forIn_seed Done s0 l b' s hb'
      refine ⟨h1, fun x hx => h2 x (hsub x hx), fun a' ha' => ?_, h4⟩
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact h2 _ ha
      · exact h3 a' ha'
    by_cases hc : b.1.contains a = true
    · refine key b h (fun _ hx => hx) hc ?_
      simp [List.forIn_cons, StateT.run, seedStep, hc, bind, StateT.bind, pure, StateT.pure]
    · refine key (b.1.insert a, b.2.enqueue a) (h.enqueue a) (fun x hx => ?_) ?_ ?_
      · show (b.1.insert a).contains x = true
        rw [Std.HashSet.contains_insert, hx, Bool.or_true]
      · show (b.1.insert a).contains a = true
        simp [Std.HashSet.contains_insert]
      · simp [List.forIn_cons, StateT.run, seedStep, hc, bind, StateT.bind, pure, StateT.pure]

/-- **A worklist run that reports itself drained has done every seed**, when processing an
    item makes it done, keeps done items done, and done is closed under `==`. -/
theorem worklist_run_complete [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done : σ → α → Prop) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (initial : List α) (cap : Nat) (s : σ)
    (hfin : ((Strata.Worklist.run initial process cap).run s).1 = true) :
    ∀ a ∈ initial, Done ((Strata.Worklist.run initial process cap).run s).2 a := by
  unfold Strata.Worklist.run at hfin ⊢
  simp only [StateT.run, bind, StateT.bind] at hfin ⊢
  have hseed := forIn_seed Done s initial (∅, ∅) s
    (fun x hx => by simp at hx)
  simp only [StateT.run] at hseed
  change (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).fst = true at hfin
  change ∀ a ∈ initial, Done (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd a
  obtain ⟨hinv, -, hall, hst⟩ := hseed
  generalize forIn initial (∅, ∅) seedStep s = r at hinv hall hst hfin ⊢
  obtain ⟨⟨S, Q⟩, s'⟩ := r
  simp only at hinv hall hst hfin ⊢
  subst hst
  intro a ha
  exact runIterations_complete Done process hmono hdone hbeq cap (Q, S) s' hinv hfin a (hall a ha)


/-! #### Closure: a drained run has done every successor of a marked item -/

/-- The enqueue step of `runOneIter`. -/
private abbrev enqStep [BEq α] [Hashable α] (x : Std.Queue α × Std.HashSet α) (b : α) :
    StateM σ (Std.Queue α × Std.HashSet α) :=
  if x.snd.contains b = true then pure (x.fst, x.snd)
  else pure (Std.Queue.enqueue b x.fst, x.snd.insert b)

/-- The enqueue fold sees every item it folds over and keeps what was seen. -/
private theorem foldlM_enqStep_seen [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] :
    ∀ (l : List α) (x : Std.Queue α × Std.HashSet α) (s : σ),
      (∀ y, x.2.contains y = true → ((l.foldlM enqStep x).run s).1.2.contains y = true) ∧
      ∀ b ∈ l, ((l.foldlM enqStep x).run s).1.2.contains b = true
  | [], x, s => ⟨fun _ h => h, fun _ hb => absurd hb List.not_mem_nil⟩
  | b :: l, x, s => by
    have key : ∀ x' : Std.Queue α × Std.HashSet α, (∀ y, x.2.contains y = true → x'.2.contains y =
        true) →
        x'.2.contains b = true → ((b :: l).foldlM enqStep x).run s = (l.foldlM enqStep x').run s →
        (∀ y, x.2.contains y = true → (((b :: l).foldlM enqStep x).run s).1.2.contains y = true) ∧
        ∀ b' ∈ b :: l, (((b :: l).foldlM enqStep x).run s).1.2.contains b' = true := by
      intro x' hsub hb heq
      rw [heq]
      obtain ⟨h1, h2⟩ := foldlM_enqStep_seen l x' s
      refine ⟨fun y hy => h1 y (hsub y hy), fun b' hb' => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h1 _ hb
      · exact h2 b' hb'
    by_cases hc : x.2.contains b = true
    · exact key x (fun _ h => h) hc (by simp [List.foldlM_cons, enqStep, hc, StateT.run, bind,
        StateT.bind, pure, StateT.pure])
    · refine key (x.1.enqueue b, x.2.insert b) (fun y hy => ?_) ?_ ?_
      · show (x.2.insert b).contains y = true
        rw [Std.HashSet.contains_insert, hy, Bool.or_true]
      · show (x.2.insert b).contains b = true
        simp [Std.HashSet.contains_insert]
      · simp [List.foldlM_cons, enqStep, hc, StateT.run, bind, StateT.bind, pure, StateT.pure]

/-- Every successor of a marked item has been seen. -/
def MarkInv [BEq α] [Hashable α] (Mark : σ → α → Prop) (next : α → List α)
    (S : Std.HashSet α) (s : σ) : Prop :=
  ∀ a, Mark s a → ∀ b ∈ next a, S.contains b = true

/-- One iteration keeps `MarkInv`, when processing `a` returns its successors and marks
    nothing but `a`. -/
private theorem runOneIter_mark [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a)
    (st : Std.Queue α × Std.HashSet α) (s : σ) (h : MarkInv Mark next st.2 s) :
    ∀ st', ((Strata.Worklist.runOneIter process st).run s).1 = some st' →
      MarkInv Mark next st'.2 ((Strata.Worklist.runOneIter process st).run s).2 := by
  unfold Strata.Worklist.runOneIter
  simp only [StateT.run, bind]
  rcases hdq : st.fst.dequeue? with _ | ⟨a, pending⟩
  · intro st' hst'
    simp [pure, StateT.pure] at hst'
  · intro st' hst'
    simp only [StateT.bind] at hst' ⊢
    have hn := hnext a s
    have hm := hmark a s
    simp only [StateT.run] at hn hm
    generalize process a s = r at hn hm hst' ⊢
    obtain ⟨news, s1⟩ := r
    simp only at hn hm hst' ⊢
    have hseen := foldlM_enqStep_seen (σ := σ) news (pending, st.snd) s1
    have hst := foldlM_state_inv (· = s1) news enqStep
      (fun b _ x s hs => by simp only [enqStep]; split <;> exact hs) (pending, st.snd) s1 rfl
    simp only [StateT.run] at hseen hst
    change ((List.foldlM enqStep (pending, st.snd) news : StateM σ _) s1 |>.fst |> some) = some st'
      at hst'
    change MarkInv Mark next st'.2 ((List.foldlM enqStep (pending, st.snd) news : StateM σ _) s1).2
    rw [hst]
    simp only [Option.some.injEq] at hst'
    subst hst'
    intro x hx b hb
    rcases hm x hx with hx | rfl
    · exact hseen.1 b (h x hx b hb)
    · exact hseen.2 b (hn b hb)

/-- Iterating keeps `CompleteInv` and `MarkInv`; when the run reports itself drained, every
    successor of a marked item is done. -/
private theorem runIterations_closed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a) :
    ∀ n (st : Std.Queue α × Std.HashSet α) s, CompleteInv Done st.1 st.2 s →
      MarkInv Mark next st.2 s →
      ((Strata.Worklist.runIterations process n st).run s).1 = true →
      ∀ a, Mark ((Strata.Worklist.runIterations process n st).run s).2 a →
        ∀ b ∈ next a, Done ((Strata.Worklist.runIterations process n st).run s).2 b
  | 0, st, s, hc, hm, hfin, a, ha, b, hb => by
    obtain ⟨pending, seen⟩ := st
    unfold Strata.Worklist.runIterations at hfin ha ⊢
    exact runIterations_complete Done process hmono hdone hbeq 0 (pending, seen) s hc
      (by unfold Strata.Worklist.runIterations; exact hfin) b (hm a ha b hb)
  | n + 1, st, s, hc, hm, hfin, a, ha, b, hb => by
    unfold Strata.Worklist.runIterations at hfin ha ⊢
    simp only [StateT.run, bind, StateT.bind] at hfin ha ⊢
    have h2 := runOneIter_complete Done process hmono hdone hbeq st s hc
    have h3 := runOneIter_mark Mark next process hnext hmark st s hm
    simp only [StateT.run] at h2 h3
    generalize Strata.Worklist.runOneIter process st s = r at h2 h3 hfin ha ⊢
    obtain ⟨o, s2⟩ := r
    rcases h2 with ⟨ho, hs2, hq⟩ | ⟨st', ho, hd⟩
    · simp only at ho hs2
      subst ho hs2
      rcases hc b (hm a ha b hb) with h | ⟨y, hy, -⟩
      · exact h
      · rw [hq] at hy; cases hy
    · simp only at ho hd
      subst ho
      exact runIterations_closed Done Mark next process hmono hdone hbeq hnext hmark n st' s2
        hd.1 (h3 st' rfl) hfin a ha b hb

/-- **A drained worklist run has done every successor of every item it marked**, when
    processing an item returns its successors, makes it done and marks only it, done items stay
    done, done is closed under `==`, and nothing is marked at the start. -/
theorem worklist_run_closed [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (Done Mark : σ → α → Prop) (next : α → List α) (process : α → StateM σ (List α))
    (hmono : ∀ a s x, Done s x → Done ((process a).run s).2 x)
    (hdone : ∀ a s, Done ((process a).run s).2 a)
    (hbeq : ∀ s x y, (x == y) = true → Done s y → Done s x)
    (hnext : ∀ a s, ∀ b ∈ next a, b ∈ ((process a).run s).1)
    (hmark : ∀ a s x, Mark ((process a).run s).2 x → Mark s x ∨ x = a)
    (initial : List α) (cap : Nat) (s : σ) (h0 : ∀ a, ¬ Mark s a)
    (hfin : ((Strata.Worklist.run initial process cap).run s).1 = true) :
    ∀ a, Mark ((Strata.Worklist.run initial process cap).run s).2 a →
      ∀ b ∈ next a, Done ((Strata.Worklist.run initial process cap).run s).2 b := by
  unfold Strata.Worklist.run at hfin ⊢
  simp only [StateT.run, bind, StateT.bind] at hfin ⊢
  have hseed := forIn_seed Done s initial (∅, ∅) s (fun x hx => by simp at hx)
  simp only [StateT.run] at hseed
  change (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).fst = true at hfin
  change ∀ a, Mark (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd a →
    ∀ b ∈ next a, Done (match forIn initial (∅, ∅) seedStep s with
      | (a, s) => Strata.Worklist.runIterations process cap (a.snd, a.fst) s).snd b
  obtain ⟨hinv, -, -, hst⟩ := hseed
  generalize forIn initial (∅, ∅) seedStep s = r at hinv hst hfin ⊢
  obtain ⟨⟨S, Q⟩, s'⟩ := r
  simp only at hinv hst hfin ⊢
  subst hst
  exact runIterations_closed Done Mark next process hmono hdone hbeq hnext hmark cap (Q, S) s'
    hinv (fun a ha => absurd ha (h0 a)) hfin

end WorklistInv

end Core.MonomorphizeFunctions
