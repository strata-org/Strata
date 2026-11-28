/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.MonomorphizeFunctions
public import Strata.Languages.Core.NameManglingProps
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
import Strata.Util.ListUtilsProps
import Strata.Util.StateMProps
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
import all Strata.DL.Lambda.LExprRenameOps
import Strata.Util.WorklistProps

/-! # Monomorphization: properties of `monomorphizeFunctions`

Everything the correctness theorems of `MonomorphizeFunctionsCorrect` rest on: how copies are
named, how a model of a factory transfers to a factory of instances of its functions, what
the steps that rewrite expressions and declarations compute, what a successful run computes,
and the model of the output's runtime factory.

## Key results

- `MangledFrom.unique`, `demangleName_mangledName` — a mangled name determines its base.
- `FnInstance.interpConsistentBody`, `FnInstance.axiomsSatisfied`,
  `FnInstance.interpConsistentEval` — an instance of a function keeps its body, axioms and
  concrete evaluator consistent with a model.
- `monoRen` — the renaming of operators the pass applies, and a model of a factory of
  instances built from a model of the original.
- `processTopDecls_decls`, `updateFunctionsInProgram_decls`, `updateFactory_run` — what the
  declaration rewriting steps make of a program and its factory.
- `run_ok` — what a successful run computes, on a program without procedures.
- `MonoPre` — what the phase needs of its input.
- `runtime_constr_cover` — every constructor of the input's runtime factory is in the output's.
- `newFn_source` — every new function is a copy of a function of the input or the factory.
- `passMono_runs` — the phase's run in the form the pipeline uses.
- `getElem?_runtimeFactoryOf_of_contributed` — a function a declaration contributes is found
  under its name in the runtime factory, when contributed names are distinct.
- `instModel` — the model of a factory of instances, as a runtime factory.
-/

public section

/-! ## Mangled names -/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling

/-- The name `mangleFuncName pfx` gives a reference to `o` at the instantiation `τs`. -/
@[expose] def mangledName (pfx o : String) (τs : List LMonoTy) : String := copyName pfx o τs

/-- `n` is the mangled name, with prefix `pfx`, of `o` at some nonempty instantiation. -/
@[expose] def MangledFrom (pfx n o : String) : Prop :=
  ∃ rest : String, n = pfx ++ monoDelim ++ escName o ++ monoDelim ++ rest

/-- A mangled name determines the name it was mangled from. -/
theorem MangledFrom.unique {pfx n o o' : String} (h : MangledFrom pfx n o)
    (h' : MangledFrom pfx n o') : o = o' := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', he⟩ := h'
  have hl := congrArg String.toList he
  simp only [String.toList_append, List.append_assoc, monoDelim] at hl
  have hl' := List.append_cancel_left hl
  have hl'' := List.append_cancel_left hl'
  exact escName_inj (String.toList_inj.mp (prefix_hash_unique (hash_not_mem_escName o)
    (hash_not_mem_escName o') (by simpa using hl'')))

/-- A mangled name starts with its prefix and `#`. -/
private theorem MangledFrom.prefix {pfx n o : String} (h : MangledFrom pfx n o) :
    (pfx ++ monoDelim).toList <+: n.toList := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨(escName o ++ monoDelim ++ r).toList, by simp [String.toList_append]⟩

/-- The name a mangled name was mangled from, and any other name itself. A model of the
    monomorphized program reads an operator `n` as the original model reads
    `demangleName pfx n`. -/
@[expose] noncomputable def demangleName (pfx n : String) : String :=
  open Classical in if h : ∃ o, MangledFrom pfx n o then Classical.choose h else n

/-- A name that does not start with the prefix and `#` demangles to itself. -/
theorem demangleName_of_not_prefix {pfx n : String}
    (h : ¬ (pfx ++ monoDelim).toList <+: n.toList) : demangleName pfx n = n := by
  unfold demangleName
  split
  · rename_i hex
    obtain ⟨o, ho⟩ := hex
    exact absurd ho.prefix h
  · rfl

/-- **The mangled name of any name demangles to that name.** The base is escaped, so this
    needs no premise on `o`; a nullary instantiation leaves `o` as is, which then must not
    start with the prefix. -/
theorem demangleName_mangledName {pfx o : String} (τs : List LMonoTy)
    (h : τs = [] → ¬ (pfx ++ monoDelim).toList <+: o.toList) :
    demangleName pfx (mangledName pfx o τs) = o := by
  unfold mangledName copyName
  split
  · exact demangleName_of_not_prefix (h (List.isEmpty_iff.mp ‹_›))
  · have hm : MangledFrom pfx (pfx ++ monoDelim ++ escName o ++ monoDelim ++ mangleTyArgs τs) o :=
      ⟨_, rfl⟩
    unfold demangleName
    split
    · rename_i hex'
      exact (Classical.choose_spec hex').unique hm
    · rename_i hno; exact absurd ⟨o, hm⟩ hno

/-! ## Models of a factory of instances

A function `g'` is an instance of `g` (`FnInstance pfx g g'`) when it is `g` with a type
substitution `S` applied to its signature, body and axioms, and then operators renamed by
some `r` that `demangleName pfx` undoes on `g`'s expressions. Reading each operator `n` as the
original model reads `demangleName pfx n` makes a model of every factory whose functions are
instances of the functions of a factory with a model (`Interp.ofInstances`). -/

variable {T : LExprParams} {pfx : String}

/-- The operator interpretation that reads every operator `n` as `op` reads
    `demangleName pfx n`. -/
@[expose] noncomputable def demangledOpInterp (pfx : String) {tc : TyConstrInterp} (op : OpInterp tc) :
    OpInterp tc :=
  fun n => op (demangleName pfx n)

/-- Rename every operator to the name it was mangled from. -/
@[expose] noncomputable def demangleRen (pfx : String) :
    Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta :=
  fun o _ => ⟨demangleName pfx o.name, o.metadata⟩

/-- Under `demangledOpInterp pfx op`, an expression denotes what it denotes under `op` with its
    operators demangled. -/
private theorem denote_demangledOpInterp {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {Δ : List LMonoTy} (bv : BVarVal tc vt Δ)
    {e : LExpr T.mono} {τ : LMonoTy} (h : e.HasTypeA Δ τ) :
    LExpr.denote tc (demangledOpInterp pfx op) fv vt bv e τ h =
      LExpr.denote tc op fv vt bv (e.renameOps (demangleRen pfx)) τ
        (LExpr.HasTypeA_renameOps (demangleRen pfx) h) :=
  (denote_renameOps (demangleRen pfx) bv h _ (fun _ _ => rfl)).symm

/-- Under `demangledOpInterp pfx op`, arguments denote what they denote under `op` with their
    operators demangled. -/
private theorem denoteArgs_demangledOpInterp {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) :
    ∀ (args : List (LExpr T.mono)) (tys : List LMonoTy)
      (h : List.Rel₂ (LExpr.HasTypeA Δ) args tys)
      (h' : List.Rel₂ (LExpr.HasTypeA Δ) (args.map (·.renameOps (demangleRen pfx))) tys),
      denoteArgs tc (demangledOpInterp pfx op) fv vt bv args tys h =
        denoteArgs tc op fv vt bv (args.map (·.renameOps (demangleRen pfx))) tys h'
  | [], [], _, _ => rfl
  | a :: as, ty :: tys, h, h' => by
    simp only [List.map_cons, denoteArgs]
    rw [denote_demangledOpInterp bv h.head,
      denoteArgs_demangledOpInterp bv as tys h.tail h'.tail]

/-- `g'` is `g` instantiated by a type substitution `S`, with operators renamed by a
    renaming `r` that `demangleName pfx` undoes on the instantiated expressions of `g`, and named
    by a name that demangles to `g`'s. Typing of the instantiated body and axioms reflects
    to the originals. Instances of a constructor are the constructor up to its expressions. -/
@[expose] def FnInstance (pfx : String) (g g' : LFunc T) : Prop :=
  ∃ (S : Subst) (r : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta),
    demangleName pfx g'.name.name = g.name.name ∧
    g'.inputs = g.inputs.map (fun p => (p.1, LMonoTy.subst S p.2)) ∧
    g'.output = LMonoTy.subst S g.output ∧
    g'.body = g.body.map (fun b => (b.applyTypeSubst S).renameOps r) ∧
    g'.axioms = g.axioms.map (fun a => (a.applyTypeSubst S).renameOps r) ∧
    g'.concreteEval = g.concreteEval ∧
    (∀ e ∈ g.body.toList ++ g.axioms, ∀ p ∈ (e.applyTypeSubst S).opAnnots,
      demangleName pfx (r p.1 (some p.2)).name = p.1.name) ∧
    (∀ b, g.body = some b → (b.applyTypeSubst S).HasTypeA [] (LMonoTy.subst S g.output) →
      b.HasTypeA [] g.output) ∧
    (∀ a ∈ g.axioms, (a.applyTypeSubst S).HasTypeA [] .bool → a.HasTypeA [] .bool)

/-- Applying heterogeneously equal functions to heterogeneously equal arguments, at equal sorts,
    gives heterogeneously equal results. -/
private theorem applyArgs_heq {tc : TyConstrInterp} {a₁ a₂ : List LSort} {r₁ r₂ : LSort}
    {f₁ : SortDenote tc (LSort.mkArrow r₁ a₁)} {f₂ : SortDenote tc (LSort.mkArrow r₂ a₂)}
    {x₁ : HList (SortDenote tc) a₁} {x₂ : HList (SortDenote tc) a₂}
    (ha : a₁ = a₂) (hr : r₁ = r₂) (hf : HEq f₁ f₂) (hx : HEq x₁ x₂) :
    HEq (SortDenote.applyArgs tc f₁ x₁) (SortDenote.applyArgs tc f₂ x₂) := by
  subst ha hr; cases hf; cases hx; rfl

/-- An operator's interpretation at two equal sorts gives heterogeneously equal values. -/
private theorem opInterp_heq {tc : TyConstrInterp} (op : OpInterp tc) (n : String)
    {s₁ s₂ : LSort} (h : s₁ = s₂) : HEq (op n s₁) (op n s₂) := by
  subst h; rfl

/-- Binding equal formals to heterogeneously equal arguments gives the same valuation. -/
private theorem withArgs_congr [DecidableEq T.IDMeta] {tc : TyConstrInterp}
    (fv : IdentInterp T tc) {b₁ b₂ : List (Identifier T.IDMeta × LSort)} (hb : b₁ = b₂)
    {x₁ : HList (SortDenote tc) (b₁.map Prod.snd)} {x₂ : HList (SortDenote tc) (b₂.map Prod.snd)}
    (hx : HEq x₁ x₂) : fv.withArgs b₁ x₁ = fv.withArgs b₂ x₂ := by
  subst hb; cases hx; rfl

/-- Denotations of one expression at two equal types are heterogeneously equal. -/
private theorem denote_heq_ty {tc : TyConstrInterp} {op : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} {e : LExpr T.mono} {τ₁ τ₂ : LMonoTy} (hτ : τ₁ = τ₂)
    (h₁ : e.HasTypeA [] τ₁) (h₂ : e.HasTypeA [] τ₂) :
    HEq (LExpr.denote tc op fv vt .nil e τ₁ h₁) (LExpr.denote tc op fv vt .nil e τ₂ h₂) := by
  subst hτ; rfl

/-- The type-variable valuation that sends a variable `S` substitutes to its image grounded
    under `vt`, and any other variable to its value under `vt`. -/
private abbrev substVal (S : Subst) (vt : TyVarVal) : TyVarVal :=
  fun x => match S.find? x with | some t => LMonoTy.substTyVars vt t | none => vt x

/-- Grounding a substituted type under `vt` is grounding the type under `substVal S vt`. -/
private theorem substTyVars_subst' (S : Subst) (vt : TyVarVal) (ty : LMonoTy) :
    LMonoTy.substTyVars vt (LMonoTy.subst S ty) = LMonoTy.substTyVars (substVal S vt) ty :=
  substTyVars_subst vt S ty

/-- The bindings of an instance's inputs at `vt` are the original's at `substVal S vt`. -/
private theorem bindings_subst (S : Subst) (vt : TyVarVal)
    (ins : List (Identifier T.IDMeta × LMonoTy)) :
    List.map (fun (x : Identifier T.IDMeta × LMonoTy) => (x.1, LMonoTy.substTyVars vt x.2))
        (ins.map (fun p => (p.1, LMonoTy.subst S p.2))) =
      List.map (fun (x : Identifier T.IDMeta × LMonoTy) =>
        (x.1, LMonoTy.substTyVars (substVal S vt) x.2)) ins := by
  simp only [List.map_map, Function.comp_def, substTyVars_subst']

/-- **Bodies.** An instance of a function consistent with its body in a model is
    consistent with its own body under the demangled interpretation. -/
theorem FnInstance.interpConsistentBody [DecidableEq T.IDMeta] {tc : TyConstrInterp}
    {op : OpInterp tc} {g g' : LFunc T}
    (hI : ∀ b, g.body = some b → LFunc.InterpConsistentBody tc op g b)
    (hrel : FnInstance pfx g g') {b' : LExpr T.mono} (hb' : g'.body = some b') :
    LFunc.InterpConsistentBody tc (demangledOpInterp pfx op) g' b' := by
  obtain ⟨S, r, hname, hin, hout, hbody, -, -, hops, htyb, -⟩ := hrel
  rw [hbody] at hb'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  intro vt fvarVal
  dsimp only
  intro h_body' args'
  have hbind := bindings_subst S vt g.inputs
  rw [← hin] at hbind
  have hsorts := congrArg (List.map Prod.snd) hbind
  have hosort : LMonoTy.substTyVars vt g'.output =
      LMonoTy.substTyVars (substVal S vt) g.output := by
    rw [hout, substTyVars_subst']
  have h_sub : (b.applyTypeSubst S).HasTypeA [] (LMonoTy.subst S g.output) :=
    (LExpr.HasTypeA_renameOps_iff r).mp (hout ▸ h_body')
  have h_b : b.HasTypeA [] g.output := htyb b hb h_sub
  have hold := hI b hb (substVal S vt) fvarVal
  dsimp only at hold
  let args := cast (congrArg (HList (SortDenote tc)) hsorts) args'
  have hargs : HEq args' args := (cast_heq _ _).symm
  have hold' := hold h_b args
  have hops' : LExpr.OpsReadAs op (demangledOpInterp pfx op) r (b.applyTypeSubst S) := by
    intro p hp
    show op (demangleName pfx (r p.1 (some p.2)).name) = op p.1.name
    rw [hops b (by simp [hb]) p hp]
  have h_td : TyDenote tc vt (LMonoTy.subst S g.output) =
      TyDenote tc (substVal S vt) g.output := by
    simp only [TyDenote, substTyVars_subst']
  apply eq_of_heq
  refine (applyArgs_heq (f₂ := op g.name.name _) hsorts (by rw [hosort]) ?_ hargs).trans ?_
  · show HEq (op (demangleName pfx g'.name.name) _) _
    rw [hname]
    exact opInterp_heq op _ (by rw [hosort, hsorts])
  rw [hold']
  refine HEq.trans ?_ (denote_heq_ty hout.symm (LExpr.HasTypeA_renameOps r h_sub) h_body')
  rw [denote_renameOps r .nil h_sub _ hops',
    denote_applyTypeSubst tc op (fvarVal.withArgs _ args') rfl h_b h_sub h_td]
  refine HEq.trans ?_ (cast_heq _ _).symm
  rw [withArgs_congr fvarVal hbind hargs]
  exact HEq.rfl

/-- **Axioms.** The axioms of an instance of a function whose axioms hold in a model hold
    under the demangled interpretation. -/
theorem FnInstance.axiomsSatisfied {tc : TyConstrInterp} {op : OpInterp tc} {g g' : LFunc T}
    (hI : ∀ ax ∈ g.axioms, ∀ (vt : TyVarVal) (fv : FreeVarVal T tc) (h : ax.HasTypeA [] .bool),
      (LExpr.denote tc op fv vt .nil ax .bool h : Bool) = true)
    (hrel : FnInstance pfx g g') :
    ∀ ax' ∈ g'.axioms, ∀ (vt : TyVarVal) (fv : FreeVarVal T tc) (h' : ax'.HasTypeA [] .bool),
      (LExpr.denote tc (demangledOpInterp pfx op) fv vt .nil ax' .bool h' : Bool) = true := by
  obtain ⟨S, r, -, -, -, -, hax, -, hops, -, htya⟩ := hrel
  intro ax' hmem vt fv h'
  rw [hax] at hmem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
  have hbool : LMonoTy.subst S .bool = .bool := LMonoTy.subst_ground S _ rfl
  have h_sub : (a.applyTypeSubst S).HasTypeA [] .bool := (LExpr.HasTypeA_renameOps_iff r).mp h'
  have h_sub' : (a.applyTypeSubst S).HasTypeA [] (LMonoTy.subst S .bool) := by
    rw [hbool]; exact h_sub
  have h_a : a.HasTypeA [] .bool := htya a ha h_sub
  have hops' : LExpr.OpsReadAs op (demangledOpInterp pfx op) r (a.applyTypeSubst S) := by
    intro p hp
    show op (demangleName pfx (r p.1 (some p.2)).name) = op p.1.name
    rw [hops a (by simp [ha]) p hp]
  have h_td : TyDenote tc vt (LMonoTy.subst S .bool) = TyDenote tc (substVal S vt) .bool := by
    simp only [TyDenote, substTyVars_subst']
  have hfin : HEq (LExpr.denote tc (demangledOpInterp pfx op) fv vt .nil
      ((a.applyTypeSubst S).renameOps r) .bool h')
      (LExpr.denote tc op fv (substVal S vt) .nil a .bool h_a) := by
    rw [denote_renameOps r .nil h_sub h' hops']
    refine (denote_heq_ty hbool.symm h_sub h_sub').trans ?_
    rw [denote_applyTypeSubst tc op fv rfl h_a h_sub' h_td]
    exact cast_heq _ _
  have := hI a ha (substVal S vt) fv h_a
  exact (eq_of_heq hfin).trans this

/-- Renaming operators keeps the typing of every argument of a list. -/
private theorem Rel₂_renameOps {Δ : List LMonoTy}
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) :
    ∀ {args : List (LExpr T.mono)} {tys : List LMonoTy},
      List.Rel₂ (LExpr.HasTypeA Δ) args tys →
      List.Rel₂ (LExpr.HasTypeA Δ) (args.map (·.renameOps g)) tys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (LExpr.HasTypeA_renameOps g h) (Rel₂_renameOps g hs)

/-- Denoting a list of arguments at two equal lists of types gives heterogeneously equal values.
    -/
private theorem denoteArgs_heq_tys {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {args : List (LExpr T.mono)}
    {tys₁ tys₂ : List LMonoTy} (htys : tys₁ = tys₂)
    (h₁ : List.Rel₂ (LExpr.HasTypeA []) args tys₁) (h₂ : List.Rel₂ (LExpr.HasTypeA []) args tys₂) :
    HEq (denoteArgs tc op fv vt .nil args tys₁ h₁) (denoteArgs tc op fv vt .nil args tys₂ h₂) := by
  subst htys; rfl

/-- One substitution that does what `S` and then `tySubst` do on an output and some input
    types. -/
private theorem exists_subst_comp (S tySubst : Subst) (out : LMonoTy) (ins : List LMonoTy) :
    ∃ τ : Subst, LMonoTy.subst tySubst (LMonoTy.subst S out) = LMonoTy.subst τ out ∧
      ins.map (fun t => LMonoTy.subst tySubst (LMonoTy.subst S t)) = ins.map (LMonoTy.subst τ) := by
  obtain ⟨τ, hτ⟩ := LMonoTy.exists_subst_subst tySubst S (.tcons "" (out :: ins))
  refine ⟨τ, ?_⟩
  simp only [LMonoTy.subst_tcons_map, List.map_cons, LMonoTy.tcons.injEq, List.cons.injEq,
    true_and, List.map_map, Function.comp_def] at hτ
  exact hτ

/-- **Concrete evaluators.** An instance of a function whose concrete evaluator is
    consistent with a model is consistent with it under the demangled interpretation,
    when the evaluator commutes with demangling. -/
theorem FnInstance.interpConsistentEval [DecidableEq T.IDMeta] {tc : TyConstrInterp}
    {op : OpInterp tc} {g g' : LFunc T} (hrel : FnInstance pfx g g')
    {c : ConcreteEval T}
    (hI : LFunc.InterpConsistentEval tc op g c)
    (hnat : ∀ md opTy args res, c md opTy args = some res →
      c md opTy (args.map (·.renameOps (demangleRen pfx))) = some (res.renameOps (demangleRen pfx))) :
    LFunc.InterpConsistentEval tc (demangledOpInterp pfx op) g' c := by
  obtain ⟨S, r, hname, hin, hout, -, -, -, -, -, -⟩ := hrel
  intro vt fvarVal md tySubst args res
  dsimp only
  intro hres h_args h_result
  obtain ⟨τ, hτo, hτi⟩ := exists_subst_comp S tySubst g.output (g.inputs.map Prod.snd)
  have hins : (List.map Prod.snd g'.inputs).map (LMonoTy.subst tySubst) =
      (List.map Prod.snd g.inputs).map (LMonoTy.subst τ) := by
    have hl : ∀ l : List (Identifier T.IDMeta × LMonoTy),
        (List.map Prod.snd (l.map (fun p => (p.1, LMonoTy.subst S p.2)))).map
          (LMonoTy.subst tySubst) =
        (l.map Prod.snd).map (fun t => LMonoTy.subst tySubst (LMonoTy.subst S t)) := by
      intro l; induction l <;> simp_all
    rw [hin, ← hτi]; exact hl g.inputs
  have hout' : LMonoTy.subst tySubst g'.output = LMonoTy.subst τ g.output := by
    rw [hout, hτo]
  rw [show g'.instTy tySubst = g.instTy τ by simp only [LFunc.instTy, hins, hout']] at hres
  have hold := hI vt fvarVal md τ _ _ (hnat md _ args res hres)
  dsimp only at hold
  have h_args0 : List.Rel₂ (LExpr.HasTypeA []) (args.map (·.renameOps (demangleRen pfx)))
      ((List.map Prod.snd g.inputs).map (LMonoTy.subst τ)) :=
    hins ▸ Rel₂_renameOps (demangleRen pfx) h_args
  have h_res0 : (res.renameOps (demangleRen pfx)).HasTypeA [] (LMonoTy.subst τ g.output) :=
    hout' ▸ LExpr.HasTypeA_renameOps (demangleRen pfx) h_result
  have hold' := hold h_args0 h_res0
  apply eq_of_heq
  rw [denote_demangledOpInterp]
  refine (denote_heq_ty hout' _ h_res0).trans ?_
  rw [hold', denoteArgs_demangledOpInterp .nil args _ h_args (Rel₂_renameOps (demangleRen pfx) h_args)]
  refine applyArgs_heq (congrArg (List.map _) hins.symm) (by rw [hout']) ?_
    (denoteArgs_heq_tys hins.symm _ _)
  show HEq (op g.name.name _) (op (demangleName pfx g'.name.name) _)
  rw [hname]
  exact opInterp_heq op _ (by rw [hout', hins])

/-- An instance of a function has the function's concrete evaluator. -/
private theorem FnInstance.concreteEval_eq {g g' : LFunc T} (hrel : FnInstance pfx g g') :
    g'.concreteEval = g.concreteEval := by
  obtain ⟨_, _, -, -, -, -, -, h, -⟩ := hrel
  exact h

/-- Demangling is a renaming every concrete evaluator of `F` commutes with. -/
@[expose] def ConcreteEvalsCommuteDemangle (pfx : String) (F : Lambda.Factory T) : Prop :=
  ∀ o (ho : o ∈ F), ∀ c, (F[o]'ho).concreteEval = some c → ∀ md opTy args res,
    c md opTy args = some res →
    c md opTy (args.map (·.renameOps (demangleRen pfx))) = some (res.renameOps (demangleRen pfx))

/-- A constructor whose name demangles to itself has the same application under the demangled
    interpretation as under the original. -/
private theorem constrApp_demangledOpInterp {tc : TyConstrInterp} (op : OpInterp tc)
    (f : LFunc T) (vt : TyVarVal)
    (args : HList (SortDenote tc) (f.inputs.values.map (LMonoTy.substTyVars vt)))
    (hname : demangleName pfx f.name.name = f.name.name) :
    constrApp tc (demangledOpInterp pfx op) f vt args = constrApp tc op f vt args := by
  simp only [constrApp, demangledOpInterp, hname]

/-- **A model of a factory of instances.** If every function of `F'` is an instance of a
    function of `F`, `F`'s concrete evaluators commute with demangling, and every
    constructor of `F'` is a constructor of `F` with a name that demangles to itself and every
    constructor of `F` is in `F'`, then `F'` has a model with the same carriers. That model
    reads each operator `n` as the model of `F` reads `demangleName pfx n`. -/
@[expose] noncomputable def Interp.ofInstances [DecidableEq T.IDMeta] {F F' : Lambda.Factory T}
    (I : Interp F)
    (hrel : ∀ n (hn : n ∈ F'), ∃ o, ∃ ho : o ∈ F, FnInstance pfx (F[o]'ho) (F'[n]'hn))
    (hnat : ConcreteEvalsCommuteDemangle pfx F)
    (hconstr : ∀ f' ∈ F'.toArray, f'.isConstr = true →
      f' ∈ F.toArray ∧ demangleName pfx f'.name.name = f'.name.name)
    (hcover : ∀ f ∈ F.toArray, f.isConstr = true → f ∈ F'.toArray) : Interp F' where
  tcInterp := I.tcInterp
  opInterp := demangledOpInterp pfx I.opInterp
  allInhabited := I.allInhabited
  interpConsistent := by
    refine ⟨fun n hn body hb => ?_, fun n hn c hc => ?_⟩
    · obtain ⟨o, ho, hr⟩ := hrel n hn
      exact hr.interpConsistentBody (fun b hb => I.interpConsistent.1 o ho b hb) hb
    · obtain ⟨o, ho, hr⟩ := hrel n hn
      have hc' : (F[o]'ho).concreteEval = some c := hr.concreteEval_eq ▸ hc
      exact hr.interpConsistentEval (I.interpConsistent.2 o ho c hc') (hnat o ho c hc')
  axiomsSatisfied := by
    intro n hn
    obtain ⟨o, ho, hr⟩ := hrel n hn
    exact hr.axiomsSatisfied (I.axiomsSatisfied o ho)
  constrConsistent := by
    refine ⟨fun f1 f2 h1 h2 c1 c2 hne vt => ?_, fun f h c vt => ?_, ?_⟩
    · have hold := I.constrConsistent.constr_disjoint f1 f2 (hconstr f1 h1 c1).1
        (hconstr f2 h2 c2).1 c1 c2 hne vt
      unfold demangledOpInterp
      rw [(hconstr f1 h1 c1).2, (hconstr f2 h2 c2).2]
      exact hold
    · have hold := I.constrConsistent.constr_injective f (hconstr f h c).1 c vt
      unfold demangledOpInterp
      rw [(hconstr f h c).2]
      exact hold
    · intro P hstep sort v hs
      obtain ⟨f', hf', hc', vt', hs'⟩ := hs
      have hsF : F.IsDatatypeSort sort := ⟨f', (hconstr f' hf' hc').1, hc', vt', hs'⟩
      refine I.constrConsistent.constr_induction P ?_ sort v hsF
      intro f hf hc vt args hall
      have hf' : f ∈ F'.toArray := hcover f hf hc
      have hall' : HList.All (fun s x => F'.IsDatatypeSort s → P s x) args := by
        refine HList.All.imp ?_ hall
        intro s x hx hsF'
        obtain ⟨g, hg, hgc, vtg, hsg⟩ := hsF'
        exact hx ⟨g, (hconstr g hg hgc).1, hgc, vtg, hsg⟩
      have hres := hstep f hf' hc vt args hall'
      rw [constrApp_demangledOpInterp I.opInterp f vt args (hconstr f hf' hc).2] at hres
      exact hres

end Core.MonomorphizeFunctions


end -- public section

/-! ## What the transformation computes -/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling Strata.PtrCache

/-- The name `rewriteLExprOp` gives an operator `o` annotated `ty`. -/
public def monoRen (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (o : CoreIdent) (ty : Option LMonoTy) : CoreIdent :=
  match P.lookup F o.name with
  | some (fdef, _) =>
    match getTypeSubstitution fdef ty with
    | some ts => ⟨mangledName P.copyPrefix o.name ts.givenTypes, ()⟩
    | none => o
  | none => o

/-- Unfolds one step of `applyOnceDFSM` with `rewriteLExprOp`, rewrites the sub-results by
    the given equations, and closes the goal. -/
local macro "dfs_step" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [StateT.run, LExpr.Traversal.applyOnceDFSM, bind, StateT.bind,
      rewriteLExprOp, pure, StateT.pure, Option.getD_none, List.nil_append, List.append_assoc,
      LExpr.renameOps, $hs,*] <;> exact ⟨_, _, rfl⟩))

/-- `applyOnceDFSM` with `rewriteLExprOp` renames every operator by `monoRen`, whatever the
    cache. -/
private theorem applyOnceDFSM_rewriteLExprOp (P : PolymorphicFuncDecls)
    (F : Lambda.Factory CoreLParams) (e : Expression.Expr) (c : PtrCache mangleTy) :
    ∃ w c', (LExpr.Traversal.applyOnceDFSM .preorder (rewriteLExprOp P F) e).run c =
      ((e.renameOps (monoRen P F), w), c') := by
  induction e generalizing c with
  | op m o ty =>
    simp only [LExpr.Traversal.applyOnceDFSM, rewriteLExprOp, LExpr.renameOps, monoRen]
    cases hl : P.lookup F o.name with
    | none => dfs_step []
    | some p =>
      obtain ⟨fdef, src⟩ := p
      cases hts : getTypeSubstitution fdef ty with
      | none => dfs_step [hts]
      | some ts =>
        dfs_step [hts, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, mangleFuncName_fst,
          Option.getD_some]
  | const | bvar | fvar => dfs_step []
  | abs m n ty b ih =>
    obtain ⟨w, c', h⟩ := ih c
    simp only [StateT.run] at h
    dfs_step [h]
  | quant _ _ _ _ _ _ ih1 ih2 | app _ _ _ ih1 ih2 | eq _ _ _ ih1 ih2 =>
    obtain ⟨w1, c1, h1⟩ := ih1 c
    obtain ⟨w2, c2, h2⟩ := ih2 c1
    simp only [StateT.run] at h1 h2
    dfs_step [h1, h2]
  | ite m x y z ih1 ih2 ih3 =>
    obtain ⟨w1, c1, h1⟩ := ih1 c
    obtain ⟨w2, c2, h2⟩ := ih2 c1
    obtain ⟨w3, c3, h3⟩ := ih3 c2
    simp only [StateT.run] at h1 h2 h3
    dfs_step [h1, h2, h3]

/-- `mangleOpsInLExpr` renames every operator by `monoRen`, whatever the cache. -/
private theorem mangleOpsInLExpr_run (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (e : Expression.Expr) (c : PtrCache mangleTy) :
    ∃ c', (mangleOpsInLExpr P F e).run c = (e.renameOps (monoRen P F), c') := by
  obtain ⟨w, c', h⟩ := applyOnceDFSM_rewriteLExprOp P F e c
  refine ⟨c', ?_⟩
  simp only [StateT.run] at h
  simp only [mangleOpsInLExpr, StateT.run, bind, StateT.bind, h, pure, StateT.pure]


/-! ## What the declaration rewriting steps compute -/

/-- What `processTopDecls` makes of a declaration other than a procedure. -/
public def topDecl (g : CoreIdent → Option LMonoTy → CoreIdent) : Decl → Decl
  | .ax a md => .ax { a with e := a.e.renameOps g } md
  | .lemma l md => .lemma { l with e := l.e.renameOps g } md
  | .distinct n es md => .distinct n (es.map (·.renameOps g)) md
  | d => d

/-- The program `processTopDecls` builds records no `usedIdentPrefixes`: the program is
    built from the rewritten declarations alone. -/
private theorem processTopDecls_usedIdentPrefixes (P : PolymorphicFuncDecls)
    (F : Lambda.Factory CoreLParams) (p : Program) (c : PtrCache mangleTy) :
    ((processTopDecls P F p).run c).1.1.usedIdentPrefixes = none := by
  unfold processTopDecls
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  split
  rfl

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
private theorem mangleOpsInFunctionDecl_run (P : PolymorphicFuncDecls)
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
    rw [ha, List.foldl_append_toArray]
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
          simp only [id, List.foldl_push_map, updDecl, hpoly, specsByFnOf]
          rfl
    | recFuncBlock fs md =>
      let hl : Function → List Function := fun f =>
        if f.typeArgs.isEmpty then [renFn (monoRen P F) f]
        else ((specsByFnOf specs).getD (idx, f.name.name) #[]).toList.map
          (fun x => renFn (monoRen P F) x.2)
      have hmem : (fs.foldl (fun acc f => acc ++ (hl f).toArray) #[]).toList = fs.flatMap hl := by
        rw [List.foldl_append_toArray]; simp
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
                    (fun x => renFn (monoRen P F) x.2) from ite_eq_right hpoly,
                  ← List.foldl_push_map]
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

/-- The copies `updateFactory` adds to the factory, with operators renamed, each marked as a
    copy of the function it specializes. -/
public def copiesOf (F : Lambda.Factory CoreLParams) (g : CoreIdent → Option LMonoTy → CoreIdent)
    (specs : Array (FuncSpecialization × Function)) : List (LFunc CoreLParams) :=
  specs.toList.map fun x =>
    { toFunc := markCopyOf x.1.name (renFn g x.2),
      concreteEval := (F.get? x.1.name).bind (·.concreteEval) }

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
      acc.push { toFunc := markCopyOf x.1.name (renFn (monoRen P F) x.2),
                 concreteEval := (F.get? x.1.name).bind (·.concreteEval) })]
    · dsimp only
      rw [List.foldl_push_map]
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

/-! ## What a successful run computes

The output of a successful `monomorphizeFunctions` run, described through its copies: each
function of the output and of the new factory is an instance of an input function. -/

open Lambda Core.NameMangling Strata.PtrCache

/-! ### The specialized copies -/

/-- A specialization `x.2` of `x.1` is a type instance, under its mangled name, of a function
    at `x.1`'s source. -/
public def IsCopyOf (pfx : String) (p : Program) (F : Lambda.Factory CoreLParams)
    (x : FuncSpecialization × Function) : Prop :=
  ∃ f ∈ x.1.functionsAt p F,
    x.2 = monomorphizeFunction f ⟨mangledName pfx x.1.name x.1.typeSubst.givenTypes, ()⟩
      x.1.typeSubst

/-- The invariant of the worklist state: every specialization recorded for the program comes
    from the program, every one recorded for the factory from the factory, and each is a copy. -/
def CopiesInv (pfx : String) (p : Program) (F : Lambda.Factory CoreLParams)
    (st : MonoWorklistState) : Prop :=
  (∀ x ∈ st.specializedFnsInProg, (∃ didx, x.1.source = .program didx) ∧ IsCopyOf pfx p F x) ∧
  (∀ x ∈ st.specializedFnsInFactory, x.1.source = .factory ∧ IsCopyOf pfx p F x)

/-- Recording the copy of a function at a specialization keeps every recorded specialization a
    copy from the right source. -/
private theorem addSpecializedFunctions_inv (P : PolymorphicFuncDecls) (p : Program)
    (F : Lambda.Factory CoreLParams) (fs : FuncSpecialization) (f : Function)
    (hf : f ∈ fs.functionsAt p F) (st : MonoWorklistState)
    (hst : CopiesInv P.copyPrefix p F st) :
    CopiesInv P.copyPrefix p F ((addSpecializedFunctions P F fs f).run st).2 := by
  have hcopy : IsCopyOf P.copyPrefix p F (fs, monomorphizeFunction f
      (mangleFuncName P.copyPrefix st.cache fs.name fs.typeSubst.givenTypes).1 fs.typeSubst) :=
    ⟨f, hf, by rw [mangleFuncName_fst]; rfl⟩
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
private theorem processFuncSpecialization_inv (P : PolymorphicFuncDecls) (p : Program)
    (F : Lambda.Factory CoreLParams) (fs : FuncSpecialization) (st : MonoWorklistState)
    (hst : CopiesInv P.copyPrefix p F st) :
    CopiesInv P.copyPrefix p F ((processFuncSpecialization P p F fs).run st).2 := by
  unfold processFuncSpecialization
  simp only [StateT.run, bind, StateT.bind]
  split
  rename_i r a s heq
  exact foldlM_state_inv_of_eq (CopiesInv P.copyPrefix p F) heq
    (fun m hm b s hs => by
      have h := addSpecializedFunctions_inv P p F fs m hm s hs
      simp only [StateT.run] at h ⊢
      simp only [StateT.bind]
      generalize addSpecializedFunctions P F fs m s = r at h ⊢
      exact h) hst

/-- What `run` computes, without the monad. -/
def runSt (p : Program) (cap : Nat) (s : Transform.CoreTransformState) :
    Except Transform.Err Program × Transform.CoreTransformState :=
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
    let calls := polyCalls polyfuncDecls F
    match growingCycle calls
        (reachedFunctions calls ((seedRefs ++ factorySeedRefs.toList).map (·.name))) with
    | some cycle => (.error (growingCycleError cycle), s)
    | none =>
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
private theorem run_eq (p : Program) (cap : Nat) (s : Transform.CoreTransformState) :
    (MonomorphizeFunctions.run p cap).run.run s = runSt p cap s := by
  unfold MonomorphizeFunctions.run runSt
  · simp only [StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      StateT.bind, pure, ExceptT.pure, StateT.pure, liftM, monadLift, MonadLift.monadLift,
      ExceptT.lift, Functor.map, StateT.map, Core.Transform.getFactory,
      Core.Transform.setFactory, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
      MonadStateOf.modifyGet, throw, throwThe, MonadExceptOf.throw]
    try dsimp only
    generalize processTopDecls (collectPolymorphicFuncDecls p s.factory) s.factory p
      PtrCache.empty = r
    obtain ⟨⟨p1, seeds⟩, c⟩ := r
    dsimp only
    generalize growingCycle _ _ = gc
    cases gc
    · dsimp only
      generalize (Strata.Worklist.run (m := StateM MonoWorklistState) (α := FuncSpecialization)
        _ _ cap) _ = w
      obtain ⟨fin, st⟩ := w
      cases fin
      · rfl
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
private theorem run_ok' {p : Program} {cap : Nat} {s s' : Transform.CoreTransformState}
    {p' : Program}
    (hnp : ∀ d ∈ p.decls, d.kind ≠ .proc)
    (h : (MonomorphizeFunctions.run p cap).run.run s = (.ok p', s')) :
    ∃ st : MonoWorklistState,
      let P := collectPolymorphicFuncDecls p s.factory
      let g := monoRen P s.factory
      CopiesInv P.copyPrefix { decls := p.decls.map (topDecl g) } s.factory st ∧
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
  · simp only [StateT.run] at h
    try dsimp only at h
    have hdecls := processTopDecls_decls (collectPolymorphicFuncDecls p s.factory) s.factory p
      hnp PtrCache.empty
    have hpfx := processTopDecls_usedIdentPrefixes (collectPolymorphicFuncDecls p s.factory)
      s.factory p PtrCache.empty
    simp only [StateT.run] at hdecls hpfx
    generalize hpt : processTopDecls (collectPolymorphicFuncDecls p s.factory) s.factory p
      PtrCache.empty = r at h hdecls hpfx
    obtain ⟨⟨p1, seeds⟩, c⟩ := r
    have hp1 : p1 = { decls := p.decls.map (topDecl (monoRen (collectPolymorphicFuncDecls p
        s.factory) s.factory)) } := by
      cases p1; simp only at hdecls hpfx; simp [hdecls, hpfx]
    subst hp1
    dsimp only at h
    split at h
    · exact absurd (congrArg Prod.fst h) (by simp)
    generalize hw : (Strata.Worklist.run (m := StateM MonoWorklistState) (α := FuncSpecialization)
      _ _ cap) _ = w at h
    have hinv : CopiesInv (collectPolymorphicFuncDecls p s.factory).copyPrefix
        { decls := p.decls.map (topDecl (monoRen
        (collectPolymorphicFuncDecls p s.factory) s.factory)) } s.factory w.2 := by
      rw [← hw]
      exact Strata.Worklist.run_inv _ _
        (fun a st hst => processFuncSpecialization_inv _ _ _ a st hst)
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
    ∃ st : MonoWorklistState,
      let P := collectPolymorphicFuncDecls p s.factory
      let g := monoRen P s.factory
      CopiesInv P.copyPrefix { decls := p.decls.map (topDecl g) } s.factory st ∧
      p'.decls = (p.decls.map (topDecl g)).zipIdx.flatMap
        (updDecl g (specsByFnOf st.specializedFnsInProg)) ∧
      s'.factory = Lambda.Factory.ofArray
        (keptOf P s.factory g ++ copiesOf s.factory g st.specializedFnsInFactory).toArray := by
  obtain ⟨st, h1, h2, h3, -⟩ := run_ok' hnp h
  exact ⟨st, h1, h2, h3⟩

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
private theorem addToRuntimeFactory_eq (F : Lambda.Factory CoreLParams) (d : Decl) :
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
private theorem runtimeFactoryOf_eq (F : Lambda.Factory CoreLParams) (decls : List Decl) :
    runtimeFactoryOf F decls = (decls.flatMap declFns).foldl Lambda.Factory.pushIfNew F := by
  induction decls generalizing F with
  | nil => rfl
  | cons d ds ih =>
    simp only [runtimeFactoryOf, List.foldl_cons, List.flatMap_cons, List.foldl_append] at ih ⊢
    rw [← addToRuntimeFactory_eq]
    exact ih _

/-- Adding a declaration to the runtime factory keeps the function found under a name. -/
private theorem getElem?_addToRuntimeFactory_of {F : Lambda.Factory CoreLParams} {n : String}
    {g : LFunc CoreLParams} (h : F[n]? = some g) (d : Decl) :
    (d.addToRuntimeFactory F)[n]? = some g := by
  rw [addToRuntimeFactory_eq]
  exact Lambda.Factory.getElem?_foldl_pushIfNew_of _ h

end RuntimeFactory

/-! ## The functions of the new factory are instances -/

section Instances

/-- The name `n` does not start with the copies' prefix `pfx` and `#`, so it is not read as a
    copy's (`demangleName_of_not_prefix`). -/
@[expose] public def NotCopyName (pfx n : String) : Prop := ¬ (pfx ++ monoDelim).toList <+: n.toList

/-- A name that does not start with `monoPrefix` is not a copy's name, whatever prefix the pass
    chose (`monoPrefix_prefix_choosePrefix`). -/
theorem notCopyName_of_not_monoPrefix {N : List String} {n : String}
    (h : ¬ monoPrefix.toList <+: n.toList) : NotCopyName (choosePrefix N) n := fun hp =>
  h ((monoPrefix_prefix_choosePrefix N).trans
    ((List.prefix_append _ _).trans (by simpa [String.toList_append] using hp)))

/-- `g` renames every operator whose name is not a copy's to a name that demangles back to it. -/
def RenOK (pfx : String) (g : CoreIdent → Option LMonoTy → CoreIdent) : Prop :=
  ∀ o ty, NotCopyName pfx o.name → demangleName pfx (g o ty).name = o.name

/-- The renaming the pass applies demangles back to every operator name that is not a copy's. -/
private theorem monoRen_ok (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams) :
    RenOK P.copyPrefix (monoRen P F) := by
  intro o ty h
  unfold monoRen
  split
  · split
    · exact demangleName_mangledName _ (fun _ => h)
    · exact demangleName_of_not_prefix h
  · exact demangleName_of_not_prefix h

/-- No operator of `e` has a copy's name. -/
@[expose] public def OpsUnmangled (pfx : String) (e : Expression.Expr) : Prop :=
  ∀ o ∈ e.getOps, NotCopyName pfx o.name

/-- No operator of `f`'s body or axioms, and not `f`'s name, has a copy's name. -/
@[expose] public def FnUnmangled (pfx : String) (f : LFunc CoreLParams) : Prop :=
  NotCopyName pfx f.name.name ∧ ∀ e ∈ f.body.toList ++ f.axioms, OpsUnmangled pfx e

/-- Every annotated operator of a substituted expression whose operators have no `#` is renamed
    by an admissible renaming to a name that demangles to it. -/
private theorem ops_ok {pfx : String} {g : CoreIdent → Option LMonoTy → CoreIdent}
    (hg : RenOK pfx g) {S : Subst} {e : Expression.Expr} (he : OpsUnmangled pfx e) :
    ∀ p ∈ (e.applyTypeSubst S).opAnnots, demangleName pfx (g p.1 (some p.2)).name = p.1.name := by
  intro p hp
  have hmem := LExpr.mem_getOps_of_opAnnots hp
  rw [LExpr.getOps_applyTypeSubst] at hmem
  exact hg _ _ (he _ hmem)

/-- A function with its operators renamed is an instance of itself. -/
private theorem fnInstance_renFn {pfx : String} {g : CoreIdent → Option LMonoTy → CoreIdent}
    (hg : RenOK pfx g) (lf : LFunc CoreLParams) (hu : FnUnmangled pfx lf) :
    FnInstance pfx lf { lf with toFunc := renFn g lf.toFunc } := by
  refine ⟨[], g, demangleName_of_not_prefix hu.1, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [renFn, LMonoTy.subst_nil]
    induction lf.inputs <;> simp_all <;> rfl
  · simp [renFn, LMonoTy.subst_nil]
  · simp [renFn, LExpr.applyTypeSubst_nil]
  · simp [renFn, LExpr.applyTypeSubst_nil]
  · intro e he; exact ops_ok hg (hu.2 e he)
  · intro b _ h; rwa [LExpr.applyTypeSubst_nil, LMonoTy.subst_nil] at h
  · intro a _ h; rwa [LExpr.applyTypeSubst_nil] at h

/-- A function is an instance of itself. -/
private theorem fnInstance_self {pfx : String} (lf : LFunc CoreLParams)
    (hu : FnUnmangled pfx lf) : FnInstance pfx lf lf := by
  refine ⟨[], fun o _ => o, demangleName_of_not_prefix hu.1, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [LMonoTy.subst_nil]
    induction lf.inputs <;> simp_all <;> rfl
  · simp [LMonoTy.subst_nil]
  · cases lf.body <;> simp [LExpr.applyTypeSubst_nil, LExpr.renameOps_id]
  · simp [LExpr.applyTypeSubst_nil, LExpr.renameOps_id]
  · intro e he p _; exact demangleName_of_not_prefix (hu.2 e he p.1 (by
      have := LExpr.mem_getOps_of_opAnnots ‹_›; rwa [LExpr.getOps_applyTypeSubst] at this))
  · intro b _ h; rwa [LExpr.applyTypeSubst_nil, LMonoTy.subst_nil] at h
  · intro a _ h; rwa [LExpr.applyTypeSubst_nil] at h

/-- The copy of a function at an instantiation is an instance of the function, when the
    function's body and axioms are well typed. -/
private theorem fnInstance_copy {pfx : String} {g : CoreIdent → Option LMonoTy → CoreIdent}
    (hg : RenOK pfx g) (lf : LFunc CoreLParams) (hu : FnUnmangled pfx lf) (ts : TypeArgsSubstitution)
    (hb : ∀ b, lf.body = some b → b.HasTypeA [] lf.output)
    (ha : ∀ a ∈ lf.axioms, a.HasTypeA [] .bool) :
    FnInstance pfx lf { toFunc := renFn g (monomorphizeFunction lf.toFunc
      ⟨mangledName pfx lf.name.name ts.givenTypes, ()⟩ ts), concreteEval := lf.concreteEval } := by
  refine ⟨ts.subst, g, demangleName_mangledName _ (fun _ => hu.1), ?_, rfl, ?_, ?_, rfl, ?_,
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
private theorem mem_specsByFnOf {specs : Array (FuncSpecialization × Function)} {j : Nat}
    {n : String}
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
private theorem mem_keptOf {P : PolymorphicFuncDecls} {F : Lambda.Factory CoreLParams}
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
@[expose] public def EvalCommutesDemangle (pfx : String) (f : LFunc CoreLParams) : Prop :=
  ∀ c, f.concreteEval = some c → ∀ md opTy args res, c md opTy args = some res →
    c md opTy (args.map (·.renameOps (demangleRen pfx))) = some (res.renameOps (demangleRen pfx))

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

/-- The prefix the pass names the copies of `p`'s functions with, over `s`'s factory
    (`choosePrefix`). -/
@[expose] public def copyPrefixOf (s : Transform.CoreTransformState) (p : Program) : String :=
  (collectPolymorphicFuncDecls p s.factory).copyPrefix

/-- **What the phase needs of its input** (state `s`, program `p`):
    - `noProcs`: `p` declares no procedure;
    - `distinct`: the functions the state's factory and `p` contribute to a runtime factory
      have pairwise distinct names;
    - `unmangled`: none of them has a name, or an operator in its body or axioms, that starts
      with the copies' prefix (`copyPrefixOf`) and `#`;
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
  unmangled : ∀ f ∈ contributed s.factory p.decls, FnUnmangled (copyPrefixOf s p) f
  typed : (∀ f ∈ s.factory.toArray, FnTyped f) ∧ ∀ f ∈ p.decls.flatMap progFns, FnTyped f.toLFunc
  evals : ∀ f ∈ contributed s.factory p.decls, EvalCommutesDemangle (copyPrefixOf s p) f
  noConstr : (∀ f ∈ s.factory.toArray, f.isConstr = false) ∧
    ∀ f ∈ p.decls.flatMap progFns, f.isConstr = false
  fragOps : ∀ n ∈ fragmentOpNames, ∃ f ∈ s.factory.toArray, f.name.name = n ∧ f.typeArgs = []
  /-- The pass's instantiations are read off ground annotations. -/
  ground : groundInstantiationsB s.factory p = true
  /-- Every type parameter of a function occurs in its signature. -/
  sigTypeArgs : sigTypeArgsB s.factory p = true
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
private theorem contributed_take_sublist (F : Lambda.Factory CoreLParams) (decls : List Decl)
    (i : Nat) :
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
  · exact Lambda.Factory.getElem?_foldl_pushIfNew_of _ (Lambda.Factory.getElem?_of_mem_toArray F f
      (Array.mem_toList_iff.mp hf))
  · refine Lambda.Factory.get?_foldl_pushIfNew_of_mem f _ F hf ?_ hd.2.1
    intro hmem
    rw [Lambda.Factory.mem_iff_mem_names, ← Array.mem_toList_iff, Array.toList_map] at hmem
    exact hd.2.2 _ hmem _ (List.mem_map_of_mem hf) rfl

/-- Every function of a runtime factory is one the base or the declarations contribute. -/
private theorem mem_contributed_of_runtimeFactoryOf {F : Lambda.Factory CoreLParams}
    {decls : List Decl}
    {f : LFunc CoreLParams}
    (hf : f ∈ (Core.Specification.Analysis.runtimeFactoryOf F decls).toArray) :
    f ∈ contributed F decls := by
  rw [runtimeFactoryOf_eq] at hf
  rcases Lambda.Factory.mem_foldl_pushIfNew _ _ _ hf with h | h
  · exact List.mem_append_left _ (Array.mem_toList_iff.mpr h)
  · exact List.mem_append_right _ h

end Pre

/-! ## Copies, case by case -/

section CopyCases

/-- A recorded copy from a function declaration is that function instantiated and renamed. -/
private theorem copy_func {pfx : String} {p : Program} {F : Lambda.Factory CoreLParams}
    {x : FuncSpecialization × Function}
    {j : Nat} {f : Function} {md} (hsrc : x.1.source = .program j) (hc : IsCopyOf pfx p F x)
    (hd : p.decls[j]? = some (.func f md)) :
    x.2 = monomorphizeFunction f ⟨mangledName pfx x.1.name x.1.typeSubst.givenTypes, ()⟩ x.1.typeSubst
        := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc, getElem!_def, hd, List.mem_singleton] at hf0
  rw [h, hf0]

/-- A recorded copy from a recursive block is a member of the block, of the copy's base name,
    instantiated and renamed. -/
private theorem copy_rec {pfx : String} {p : Program} {F : Lambda.Factory CoreLParams}
    {x : FuncSpecialization × Function}
    {j : Nat} {ms : List Function} {md} (hsrc : x.1.source = .program j) (hc : IsCopyOf pfx p F x)
    (hd : p.decls[j]? = some (.recFuncBlock ms md)) :
    ∃ f0 ∈ ms, f0.name.name = x.1.name ∧
      x.2 = monomorphizeFunction f0 ⟨mangledName pfx x.1.name x.1.typeSubst.givenTypes, ()⟩
          x.1.typeSubst := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc, getElem!_def, hd, List.mem_filter,
    beq_iff_eq] at hf0
  exact ⟨f0, hf0.1, hf0.2, h⟩

/-- A recorded copy from the factory is the factory's function of the copy's base name,
    instantiated and renamed. -/
private theorem copy_factory {pfx : String} {p : Program} {F : Lambda.Factory CoreLParams}
    {x : FuncSpecialization × Function} (hsrc : x.1.source = .factory) (hc : IsCopyOf pfx p F x) :
    ∃ lf, F[x.1.name]? = some lf ∧ lf.name.name = x.1.name ∧
      x.2 = monomorphizeFunction lf.toFunc ⟨mangledName pfx x.1.name x.1.typeSubst.givenTypes, ()⟩
        x.1.typeSubst := by
  obtain ⟨f0, hf0, h⟩ := hc
  simp only [FuncSpecialization.functionsAt, hsrc] at hf0
  split at hf0
  · rename_i lf hlf
    simp only [List.mem_singleton] at hf0
    exact ⟨lf, hlf, Lambda.Factory.getElem?_name hlf, by rw [h, hf0]⟩
  · simp at hf0

end CopyCases

/-! ## Every function of the new runtime factory is an instance of one of the old -/

section NewFns

/-- A function a declaration declares is among the program's declared functions. -/
private theorem mem_progFns {decls : List Decl} {d : Decl} (hd : d ∈ decls) {f : Function}
    (hf : f ∈ progFns d) : f ∈ decls.flatMap progFns :=
  List.mem_flatMap.mpr ⟨d, hd, hf⟩

/-- Every constructor of the input's runtime factory is in the output's. A constructor comes
    from a datatype declaration, which the pass keeps; the output function of the
    constructor's name is an instance of the function of that name, hence the constructor
    itself. -/
theorem runtime_constr_cover {s s' : Transform.CoreTransformState} {p p' : Program}
    (hpre : MonoPre s p) {g : CoreIdent → Option LMonoTy → CoreIdent}
    {m : Std.HashMap (Nat × String) (Array (FuncSpecialization × Function))}
    (hdecls : p'.decls = (p.decls.map (topDecl g)).zipIdx.flatMap (updDecl g m))
    (hdist : ((contributed s.factory p.decls).map (·.name.name)).Nodup)
    (hsrc : ∀ f', f' ∈
      (Core.Specification.Analysis.runtimeFactoryOf s'.factory p'.decls).toArray →
      ∃ lf ∈ contributed s.factory p.decls, FnInstance (copyPrefixOf s p) lf f' ∧
        ((f'.isConstr = true → f' = lf) ∧ (lf.isConstr = true → f' = lf))) :
    ∀ f ∈ (Core.Specification.Analysis.runtimeFactoryOf s.factory p.decls).toArray,
      f.isConstr = true →
      f ∈ (Core.Specification.Analysis.runtimeFactoryOf s'.factory p'.decls).toArray := by
  intro f hf hfc
  have hcon : f ∈ contributed s.factory p.decls := mem_contributed_of_runtimeFactoryOf hf
  -- A constructor of the runtime factory comes from a datatype declaration.
  have hdecl : ∃ d ∈ p.decls, f ∈ declFns d := by
    rcases List.mem_append.mp hcon with hb | hd
    · have hnc := hpre.noConstr.1 f (Array.mem_toList_iff.mp hb)
      rw [hnc] at hfc
      cases hfc
    · obtain ⟨d, hd, hfd⟩ := List.mem_flatMap.mp hd
      exact ⟨d, hd, hfd⟩
  obtain ⟨d, hd, hfd⟩ := hdecl
  have hd' : d ∈ p'.decls := by
    cases d with
    | func f0 md =>
      have hpf : f0 ∈ progFns (.func f0 md) := by simp [progFns]
      have hnc := hpre.noConstr.2 f0 (mem_progFns hd hpf)
      simp only [declFns, List.mem_singleton] at hfd
      subst hfd
      simp [LFuncDefined.toLFunc, hnc] at hfc
    | recFuncBlock fs md =>
      simp only [declFns, List.mem_map] at hfd
      obtain ⟨f0, hf0, rfl⟩ := hfd
      have hpf : f0 ∈ progFns (.recFuncBlock fs md) := by simpa [progFns] using hf0
      have hnc := hpre.noConstr.2 f0 (mem_progFns hd hpf)
      simp [LFuncDefined.toLFunc, hnc] at hfc
    | type t md =>
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
      have hjm : (p.decls.map (topDecl g))[j]? = some (.type t md) := by
        simp [hj, topDecl]
      have hz : ((.type t md : Decl), j) ∈ (p.decls.map (topDecl g)).zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hjm
      have hup : (.type t md : Decl) ∈ updDecl g m (.type t md, j) := by simp [updDecl]
      rw [hdecls]
      exact List.mem_flatMap.mpr ⟨_, hz, hup⟩
    | _ => simp [declFns] at hfd
  have hfL : f ∈ p'.decls.flatMap declFns := List.mem_flatMap.mpr ⟨d, hd', hfd⟩
  -- Some function of the new runtime factory has the constructor's name.
  have hsome :
      ((Core.Specification.Analysis.runtimeFactoryOf s'.factory p'.decls)[f.name.name]?).isSome =
        true := by
    rw [runtimeFactoryOf_eq, Lambda.Factory.getElem?_foldl_pushIfNew]
    have hfname : (f.name.name == f.name.name) = true := by simp
    have hfind : ((p'.decls.flatMap declFns).find? (fun h => h.name.name == f.name.name)).isSome =
        true := List.find?_isSome.mpr ⟨f, hfL, hfname⟩
    cases s'.factory[f.name.name]?
    · rw [Option.none_or]
      exact hfind
    · rw [Option.some_or]
      rfl
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hsome
  have hhmem : h ∈ (Core.Specification.Analysis.runtimeFactoryOf s'.factory p'.decls).toArray :=
    Lambda.Factory.getElem?_is_some_implies_mem hh
  have hhname : h.name.name = f.name.name := Lambda.Factory.getElem?_name hh
  -- That function is an instance of a function with the same name, hence of `f` itself.
  obtain ⟨lf, hlf, hinst, -, hlfc⟩ := hsrc h hhmem
  obtain ⟨S, r, hdem, -⟩ := hinst
  have hlfname : lf.name.name = f.name.name := by
    rw [← hdem, hhname]
    exact demangleName_of_not_prefix (hpre.unmangled f hcon).1
  have hlff : lf = f :=
    List.nodup_map_injOn hdist hlf hcon hlfname
  subst hlff
  have hhf : h = lf := hlfc hfc
  rw [← hhf]
  exact hhmem

/-- A function a declaration before index `i` contributes is among those the declarations before
    `i` contribute. -/
private theorem mem_declPart_take {decls : List Decl} {i j : Nat}
    {d : Decl} (hj : j < i) (hd : decls[j]? = some d) {f : LFunc CoreLParams}
    (hf : f ∈ declFns d) : f ∈ (decls.take i).flatMap declFns :=
  List.mem_flatMap.mpr ⟨d, List.mem_take_of_getElem? hj hd, hf⟩

/-- Every function of the new state's factory is an instance of a function of the old one, and
    the same constructor if either is a constructor. -/
private theorem newFn_source_base {s : Transform.CoreTransformState} {p : Program}
    (hpre : MonoPre s p)
    {P : PolymorphicFuncDecls} {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK (copyPrefixOf s p) g)
    {st : MonoWorklistState}
    (hinv : CopiesInv (copyPrefixOf s p) { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hb : f' ∈ (Lambda.Factory.ofArray (keptOf P s.factory g ++ copiesOf s.factory g
          st.specializedFnsInFactory).toArray).toArray.toList) :
    ∃ lf ∈ s.factory.toArray.toList, FnInstance (copyPrefixOf s p) lf f' ∧
      ((f'.isConstr = true → f' = lf) ∧ (lf.isConstr = true → f' = lf)) := by
  have hsub := contributed_take_sublist s.factory p.decls i
  have hun : ∀ lf ∈ contributed s.factory (p.decls.take i), FnUnmangled (copyPrefixOf s p) lf :=
    fun lf h => hpre.unmangled lf (hsub.subset h)
  have hb' := Lambda.Factory.ofArray_mem (Array.mem_toList_iff.mp hb)
  rw [List.mem_toArray, List.mem_append] at hb'
  rcases hb' with hk | hc
  · obtain ⟨lf, hlf, rfl⟩ := mem_keptOf hk
    have hlf' : lf ∈ contributed s.factory (p.decls.take i) :=
      List.mem_append_left _ (Array.mem_toList_iff.mpr hlf)
    have hnc := hpre.noConstr.1 lf hlf
    have hncT : ¬ lf.isConstr = true := by simp [hnc]
    refine ⟨lf, Array.mem_toList_iff.mpr hlf, fnInstance_renFn hg lf (hun lf hlf'),
      fun hc => ?_, fun hc => absurd hc hncT⟩
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
    have hnc := hpre.noConstr.1 lf hlfm
    have hncT : ¬ lf.isConstr = true := by simp [hnc]
    refine ⟨lf, Array.mem_toList_iff.mpr hlfm, fnInstance_copy hg lf (hun lf hlf') _ (hpre.typed.1
        lf hlfm).1
      (hpre.typed.1 lf hlfm).2, fun hc => ?_, fun hc => absurd hc hncT⟩
    simp only [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst] at hc
    rw [hnc] at hc; cases hc

/-- Every function the output's declarations before index `i` contribute is an instance of one
    the input's declarations before `i` contribute, and the same constructor if either is a
    constructor. -/
private theorem newFn_source_decls {s : Transform.CoreTransformState} {p : Program}
    (hpre : MonoPre s p)
    {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK (copyPrefixOf s p) g)
    {st : MonoWorklistState}
    (hinv : CopiesInv (copyPrefixOf s p) { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hd : f' ∈ (((p.decls.map (topDecl g)).zipIdx.take i).flatMap
          (updDecl g (specsByFnOf st.specializedFnsInProg))).flatMap declFns) :
    ∃ lf ∈ (p.decls.take i).flatMap declFns, FnInstance (copyPrefixOf s p) lf f' ∧
      ((f'.isConstr = true → f' = lf) ∧ (lf.isConstr = true → f' = lf)) := by
  have hsub := contributed_take_sublist s.factory p.decls i
  have hun : ∀ lf ∈ contributed s.factory (p.decls.take i), FnUnmangled (copyPrefixOf s p) lf :=
    fun lf h => hpre.unmangled lf (hsub.subset h)
  obtain ⟨d', hd', hf'd⟩ := List.mem_flatMap.mp hd
  obtain ⟨⟨dT, j⟩, hx, hd'u⟩ := List.mem_flatMap.mp hd'
  obtain ⟨hj, hdT⟩ := List.mem_take_zipIdx hx
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
      have hncT : ¬ f.toLFunc.isConstr = true := by simp [LFuncDefined.toLFunc, hnc]
      refine ⟨f.toLFunc, hlf, fnInstance_renFn hg f.toLFunc (hun _ (List.mem_append_right _ hlf)),
          fun hc => ?_, fun hc => absurd hc hncT⟩
      simp [renFn, LFuncDefined.toLFunc, hnc] at hc
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd'u
      obtain ⟨hyS, hysrc, hyname⟩ := mem_specsByFnOf hy
      obtain ⟨-, hcopy⟩ := hinv.1 y hyS
      have hy2 := copy_func hysrc hcopy hp1
      simp only [declFns, List.mem_singleton] at hf'd
      subst hf'd
      rw [hy2, hyname]
      have hncT : ¬ f.toLFunc.isConstr = true := by simp [LFuncDefined.toLFunc, hnc]
      refine ⟨f.toLFunc, hlf, fnInstance_copy hg f.toLFunc (hun _ (List.mem_append_right _ hlf)) _
        (hpre.typed.2 f hfp).1 (hpre.typed.2 f hfp).2, fun hc => ?_, fun hc => absurd hc hncT⟩
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
        have hncT : ¬ f.toLFunc.isConstr = true := by
          simp [LFuncDefined.toLFunc, hpre.noConstr.2 f hfp]
        refine ⟨f.toLFunc, hlf, fnInstance_renFn hg f.toLFunc (hun _ (List.mem_append_right _
            hlf)), fun hc => ?_, fun hc => absurd hc hncT⟩
        simp [renFn, LFuncDefined.toLFunc, hpre.noConstr.2 f hfp] at hc
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmf
        obtain ⟨hyS, hysrc, -⟩ := mem_specsByFnOf hy
        obtain ⟨-, hcopy⟩ := hinv.1 y hyS
        obtain ⟨f0, hf0, hname, hy2⟩ := copy_rec hysrc hcopy hp1
        obtain ⟨hlf, hfp⟩ := mk f0 hf0
        rw [hy2, ← hname]
        have hncT : ¬ f0.toLFunc.isConstr = true := by
          simp [LFuncDefined.toLFunc, hpre.noConstr.2 f0 hfp]
        refine ⟨f0.toLFunc, hlf, fnInstance_copy hg f0.toLFunc (hun _ (List.mem_append_right _
            hlf)) _
          (hpre.typed.2 f0 hfp).1 (hpre.typed.2 f0 hfp).2, fun hc => ?_, fun hc => absurd hc hncT⟩
        simp [renFn, monomorphizeFunction, Lambda.LFuncDefined.applyTypeSubst,
          LFuncDefined.toLFunc, hpre.noConstr.2 f0 hfp] at hc
  | type t md =>
    simp only [topDecl, updDecl, List.mem_singleton] at hd'u
    subst hd'u
    have hlf : f' ∈ (p.decls.take i).flatMap declFns := mem_declPart_take hj hd0 hf'd
    exact ⟨f', hlf, fnInstance_self f' (hun _ (List.mem_append_right _ hlf)),
      fun _ => rfl, fun _ => rfl⟩
  | _ =>
    simp only [topDecl, updDecl, List.mem_singleton] at hd'u
    subst hd'u
    simp [declFns] at hf'd

/-- Every function of the output's runtime factory before index `i` is an instance of a function
    of the input's, and the same constructor if either is a constructor. -/
theorem newFn_source {s : Transform.CoreTransformState} {p : Program} (hpre : MonoPre s p)
    {P : PolymorphicFuncDecls} {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK (copyPrefixOf s p) g)
    {st : MonoWorklistState}
    (hinv : CopiesInv (copyPrefixOf s p) { decls := p.decls.map (topDecl g) } s.factory st)
    (i : Nat) {f' : LFunc CoreLParams}
    (hf' : f' ∈ contributed
        (Lambda.Factory.ofArray (keptOf P s.factory g ++ copiesOf s.factory g
          st.specializedFnsInFactory).toArray)
        (((p.decls.map (topDecl g)).zipIdx.take i).flatMap
          (updDecl g (specsByFnOf st.specializedFnsInProg)))) :
    ∃ lf ∈ contributed s.factory (p.decls.take i), FnInstance (copyPrefixOf s p) lf f' ∧
      ((f'.isConstr = true → f' = lf) ∧ (lf.isConstr = true → f' = lf)) := by
  rcases List.mem_append.mp hf' with hb | hd
  · obtain ⟨lf, hlf, h1, h2⟩ := newFn_source_base hpre hg hinv i hb
    exact ⟨lf, List.mem_append_left _ hlf, h1, h2⟩
  · obtain ⟨lf, hlf, h1, h2⟩ := newFn_source_decls hpre hg hinv i hd
    exact ⟨lf, List.mem_append_right _ hlf, h1, h2⟩

end NewFns

/-! ## Assembling the entry -/

section Assembly

/-- No operator of a declaration's own expressions has a copy's name: its name is among the names
    the copies' prefix is chosen against (`avoidNames`), so it does not start with the prefix
    (`choosePrefix_fresh`). -/
private theorem opsUnmangled_of_mem {s : Transform.CoreTransformState} {p : Program} {d : Decl}
    (hd : d ∈ p.decls) {e : Expression.Expr} (he : e ∈ d.ownExprs) :
    OpsUnmangled (copyPrefixOf s p) e := by
  intro o ho
  have hmem : o.name ∈ checkedNames p := by
    unfold checkedNames
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, ?_⟩)
    exact List.mem_flatMap.mpr ⟨e, List.mem_append_right _ he, List.mem_append_left _
        (List.mem_map_of_mem ho)⟩
  have havoid : o.name ∈ avoidNames p s.factory := by simp [avoidNames, hmem]
  exact choosePrefix_fresh _ _ havoid

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

/-! ## The model of a factory of instances, as a runtime factory -/

section InstModel

open Core.Specification.Analysis

/-- The model of a factory of instances, as a runtime factory. -/
noncomputable def instModel {pfx : String} (M : ModeledFactory CoreLParams)
    {F' : Lambda.Factory CoreLParams}
    (hrel : ∀ n (hn : n ∈ F'), ∃ o, ∃ ho : o ∈ M.factory, FnInstance pfx (M.factory[o]'ho) (F'[n]'hn))
    (hnat : ConcreteEvalsCommuteDemangle pfx M.factory)
    (hconstr : ∀ f' ∈ F'.toArray, f'.isConstr = true →
      f' ∈ M.factory.toArray ∧ demangleName pfx f'.name.name = f'.name.name)
    (hcover : ∀ f ∈ M.factory.toArray, f.isConstr = true → f ∈ F'.toArray) :
    ModeledFactory CoreLParams :=
  ⟨F', Interp.ofInstances M.model hrel hnat hconstr hcover, M.tyVarVal⟩

/-- Renaming the operators of an expression without `#` keeps its value from the old model to
    the model of instances. -/
private theorem eval_instModel {pfx : String} {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK pfx g)
    (M : ModeledFactory CoreLParams) {F' : Lambda.Factory CoreLParams} {hrel hnat hconstr hcover}
    (σ : ValStore CoreLParams) {e : Expression.Expr} (he : OpsUnmangled pfx e) :
    (e.renameOps g).denoteEval (instModel (pfx := pfx) M (F' := F') hrel hnat hconstr hcover) σ =
      e.denoteEval M σ := by
  refine LExpr.denoteEval_renameOps (M := M) (M' := instModel M hrel hnat hconstr hcover) g σ e
    rfl HEq.rfl rfl ?_
  intro q hq
  show HEq (M.model.opInterp (demangleName pfx (g q.1 (some q.2)).name)) _
  rw [hg _ _ (he _ (LExpr.mem_getOps_of_opAnnots hq))]

/-- The disequality of two expressions whose operators have no `#` has no operator with `#`. -/
private theorem opsUnmangled_distinctPairExpr {pfx : String} {a b : Expression.Expr} (ha : OpsUnmangled pfx a)
    (hb : OpsUnmangled pfx b) : OpsUnmangled pfx (distinctPairExpr a b) := by
  intro o ho
  simp only [distinctPairExpr, LExpr.getOps, LExpr.boolConst, List.append_nil,
    List.mem_append] at ho
  rcases ho with ho | ho
  · exact ha o ho
  · exact hb o ho

end InstModel

end Core.MonomorphizeFunctions
