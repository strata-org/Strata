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
import all Strata.DL.Lambda.LExprRenameOps

/-! # Monomorphization: mangled names and models of instances

The basic facts the correctness proof of `monomorphizeFunctions` builds on: how copies are
named, and how a model of a factory transfers to a factory of instances of its functions.

## Key results

- `MangledFrom.unique`, `demangleName_mangledName` — a mangled name determines its base.
- `FnInstance.interpConsistentBody`, `FnInstance.axiomsSatisfied`,
  `FnInstance.interpConsistentEval` — an instance of a function keeps its body, axioms and
  concrete evaluator consistent with a model.
- `monoRen` — the renaming of operators the pass applies, and a model of a factory of
  instances built from a model of the original.
-/

public section

/-! ## Mangled names -/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling

/-- The name `mangleFuncName` gives a reference to `o` at the instantiation `τs`. -/
@[expose] def mangledName (o : String) (τs : List LMonoTy) : String :=
  if τs.isEmpty then o else monoPrefix ++ monoDelim ++ o ++ monoDelim ++ mangleTyArgs τs

/-- `mangleFuncName` gives `mangledName`, whatever its cache. -/
theorem mangleFuncName_fst (c : Strata.PtrCache.PtrCache mangleTy) (o : String)
    (τs : List LMonoTy) : (mangleFuncName c o τs).1 = ⟨mangledName o τs, ()⟩ := by
  unfold mangleFuncName mangledName
  split
  · rfl
  · generalize (mangleTyArgsPtrCache τs).run c = r
    obtain ⟨⟨out, hout⟩, c'⟩ := r
    simp [hout]

/-- `n` is the mangled name of `o` at some nonempty instantiation, and `o` has no `#`. -/
@[expose] def MangledFrom (n o : String) : Prop :=
  '#' ∉ o.toList ∧ ∃ rest : String, n = monoPrefix ++ monoDelim ++ o ++ monoDelim ++ rest

/-- Two character lists without `#`, each followed by `#`, are equal when what follows makes the
    two whole lists equal. -/
private theorem list_prefix_hash_unique :
    ∀ {a a' b b' : List Char}, '#' ∉ a → '#' ∉ a' →
      a ++ '#' :: b = a' ++ '#' :: b' → a = a'
  | [], [], _, _, _, _, _ => rfl
  | [], c :: _, _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | c :: _, [], _, _, h, _, hh => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hh
    exact absurd (hh.1 ▸ List.mem_cons_self) h
  | c :: a, c' :: a', b, b', h, h', hh => by
    simp only [List.cons_append, List.cons.injEq] at hh
    obtain ⟨rfl, hh⟩ := hh
    rw [list_prefix_hash_unique (fun hm => h (List.mem_cons_of_mem _ hm))
      (fun hm => h' (List.mem_cons_of_mem _ hm)) hh]

/-- A mangled name determines the name it was mangled from. -/
theorem MangledFrom.unique {n o o' : String} (h : MangledFrom n o) (h' : MangledFrom n o') :
    o = o' := by
  obtain ⟨ho, r, rfl⟩ := h
  obtain ⟨ho', r', he⟩ := h'
  have hl := congrArg String.toList he
  simp only [String.toList_append, List.append_assoc, monoPrefix, monoDelim] at hl
  have hl' := List.append_cancel_left hl
  have hl'' := List.append_cancel_left hl'
  exact String.toList_inj.mp (list_prefix_hash_unique ho ho' (by simpa using hl''))

/-- A mangled name contains `#`. -/
private theorem MangledFrom.hash_mem {n o : String} (h : MangledFrom n o) : '#' ∈ n.toList := by
  obtain ⟨_, r, rfl⟩ := h
  simp [String.toList_append, monoPrefix, monoDelim]

/-- The name a mangled name was mangled from, and any other name itself. A model of the
    monomorphized program reads an operator `n` as the original model reads
    `demangleName n`. -/
@[expose] noncomputable def demangleName (n : String) : String :=
  open Classical in if h : ∃ o, MangledFrom n o then Classical.choose h else n

/-- A name without `#` demangles to itself. -/
theorem demangleName_of_not_hash {n : String} (h : '#' ∉ n.toList) : demangleName n = n := by
  unfold demangleName
  split
  · rename_i hex
    obtain ⟨o, ho⟩ := hex
    exact absurd ho.hash_mem h
  · rfl

/-- The mangled name of a name without `#` demangles to that name. -/
theorem demangleName_mangledName {o : String} (h : '#' ∉ o.toList) (τs : List LMonoTy) :
    demangleName (mangledName o τs) = o := by
  unfold mangledName
  split
  · exact demangleName_of_not_hash h
  · have hm : MangledFrom (monoPrefix ++ monoDelim ++ o ++ monoDelim ++ mangleTyArgs τs) o :=
      ⟨h, _, rfl⟩
    have hex : ∃ o', MangledFrom (monoPrefix ++ monoDelim ++ o ++ monoDelim ++ mangleTyArgs τs) o'
        :=
      ⟨o, hm⟩
    unfold demangleName
    split
    · rename_i hex'
      exact (Classical.choose_spec hex').unique hm
    · exact absurd hex ‹_›

/-! ## Models of a factory of instances

A function `g'` is an instance of `g` (`FnInstance g g'`) when it is `g` with a type
substitution `S` applied to its signature, body and axioms, and then operators renamed by
some `r` that `demangleName` undoes on `g`'s expressions. Reading each operator `n` as the
original model reads `demangleName n` makes a model of every factory whose functions are
instances of the functions of a factory with a model (`Interp.ofInstances`). -/

variable {T : LExprParams}

/-- The operator interpretation that reads every operator `n` as `op` reads
    `demangleName n`. -/
@[expose] noncomputable def demangledOpInterp {tc : TyConstrInterp} (op : OpInterp tc) :
    OpInterp tc :=
  fun n => op (demangleName n)

/-- Rename every operator to the name it was mangled from. -/
@[expose] noncomputable def demangleRen : Identifier T.IDMeta → Option LMonoTy → Identifier
    T.IDMeta :=
  fun o _ => ⟨demangleName o.name, o.metadata⟩

/-- Under `demangledOpInterp op`, an expression denotes what it denotes under `op` with its
    operators demangled. -/
private theorem denote_demangledOpInterp {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {Δ : List LMonoTy} (bv : BVarVal tc vt Δ)
    {e : LExpr T.mono} {τ : LMonoTy} (h : e.HasTypeA Δ τ) :
    LExpr.denote tc (demangledOpInterp op) fv vt bv e τ h =
      LExpr.denote tc op fv vt bv (e.renameOps demangleRen) τ
        (LExpr.HasTypeA_renameOps demangleRen h) :=
  (denote_renameOps demangleRen bv h _ (fun _ _ => rfl)).symm

/-- Under `demangledOpInterp op`, arguments denote what they denote under `op` with their
    operators demangled. -/
private theorem denoteArgs_demangledOpInterp {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) :
    ∀ (args : List (LExpr T.mono)) (tys : List LMonoTy)
      (h : List.Rel₂ (LExpr.HasTypeA Δ) args tys)
      (h' : List.Rel₂ (LExpr.HasTypeA Δ) (args.map (·.renameOps demangleRen)) tys),
      denoteArgs tc (demangledOpInterp op) fv vt bv args tys h =
        denoteArgs tc op fv vt bv (args.map (·.renameOps demangleRen)) tys h'
  | [], [], _, _ => rfl
  | a :: as, ty :: tys, h, h' => by
    simp only [List.map_cons, denoteArgs]
    rw [denote_demangledOpInterp bv h.head,
      denoteArgs_demangledOpInterp bv as tys h.tail h'.tail]

/-- `g'` is `g` instantiated by a type substitution `S`, with operators renamed by a
    renaming `r` that `demangleName` undoes on the instantiated expressions of `g`, and named
    by a name that demangles to `g`'s. Typing of the instantiated body and axioms reflects
    to the originals. Instances of a constructor are the constructor up to its expressions. -/
@[expose] def FnInstance (g g' : LFunc T) : Prop :=
  ∃ (S : Subst) (r : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta),
    demangleName g'.name.name = g.name.name ∧
    g'.inputs = g.inputs.map (fun p => (p.1, LMonoTy.subst S p.2)) ∧
    g'.output = LMonoTy.subst S g.output ∧
    g'.body = g.body.map (fun b => (b.applyTypeSubst S).renameOps r) ∧
    g'.axioms = g.axioms.map (fun a => (a.applyTypeSubst S).renameOps r) ∧
    g'.concreteEval = g.concreteEval ∧
    (∀ e ∈ g.body.toList ++ g.axioms, ∀ p ∈ (e.applyTypeSubst S).opAnnots,
      demangleName (r p.1 (some p.2)).name = p.1.name) ∧
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
    (hrel : FnInstance g g') {b' : LExpr T.mono} (hb' : g'.body = some b') :
    LFunc.InterpConsistentBody tc (demangledOpInterp op) g' b' := by
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
  have hops' : LExpr.OpsReadAs op (demangledOpInterp op) r (b.applyTypeSubst S) := by
    intro p hp
    show op (demangleName (r p.1 (some p.2)).name) = op p.1.name
    rw [hops b (by simp [hb]) p hp]
  have h_td : TyDenote tc vt (LMonoTy.subst S g.output) =
      TyDenote tc (substVal S vt) g.output := by
    simp only [TyDenote, substTyVars_subst']
  apply eq_of_heq
  refine (applyArgs_heq (f₂ := op g.name.name _) hsorts (by rw [hosort]) ?_ hargs).trans ?_
  · show HEq (op (demangleName g'.name.name) _) _
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
    (hrel : FnInstance g g') :
    ∀ ax' ∈ g'.axioms, ∀ (vt : TyVarVal) (fv : FreeVarVal T tc) (h' : ax'.HasTypeA [] .bool),
      (LExpr.denote tc (demangledOpInterp op) fv vt .nil ax' .bool h' : Bool) = true := by
  obtain ⟨S, r, -, -, -, -, hax, -, hops, -, htya⟩ := hrel
  intro ax' hmem vt fv h'
  rw [hax] at hmem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
  have hbool : LMonoTy.subst S .bool = .bool := LMonoTy.subst_ground S _ rfl
  have h_sub : (a.applyTypeSubst S).HasTypeA [] .bool := (LExpr.HasTypeA_renameOps_iff r).mp h'
  have h_sub' : (a.applyTypeSubst S).HasTypeA [] (LMonoTy.subst S .bool) := by
    rw [hbool]; exact h_sub
  have h_a : a.HasTypeA [] .bool := htya a ha h_sub
  have hops' : LExpr.OpsReadAs op (demangledOpInterp op) r (a.applyTypeSubst S) := by
    intro p hp
    show op (demangleName (r p.1 (some p.2)).name) = op p.1.name
    rw [hops a (by simp [ha]) p hp]
  have h_td : TyDenote tc vt (LMonoTy.subst S .bool) = TyDenote tc (substVal S vt) .bool := by
    simp only [TyDenote, substTyVars_subst']
  have hfin : HEq (LExpr.denote tc (demangledOpInterp op) fv vt .nil
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
    {op : OpInterp tc} {g g' : LFunc T} (hrel : FnInstance g g')
    {c : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)}
    (hI : LFunc.InterpConsistentEval tc op g c)
    (hnat : ∀ md args res, c md args = some res →
      c md (args.map (·.renameOps demangleRen)) = some (res.renameOps demangleRen)) :
    LFunc.InterpConsistentEval tc (demangledOpInterp op) g' c := by
  obtain ⟨S, r, hname, hin, hout, -, -, -, -, -, -⟩ := hrel
  intro vt fvarVal md tySubst args res hres
  dsimp only
  intro h_args h_result
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
  have hold := hI vt fvarVal md τ _ _ (hnat md args res hres)
  dsimp only at hold
  have h_args0 : List.Rel₂ (LExpr.HasTypeA []) (args.map (·.renameOps demangleRen))
      ((List.map Prod.snd g.inputs).map (LMonoTy.subst τ)) :=
    hins ▸ Rel₂_renameOps demangleRen h_args
  have h_res0 : (res.renameOps demangleRen).HasTypeA [] (LMonoTy.subst τ g.output) :=
    hout' ▸ LExpr.HasTypeA_renameOps demangleRen h_result
  have hold' := hold h_args0 h_res0
  apply eq_of_heq
  rw [denote_demangledOpInterp]
  refine (denote_heq_ty hout' _ h_res0).trans ?_
  rw [hold', denoteArgs_demangledOpInterp .nil args _ h_args (Rel₂_renameOps demangleRen h_args)]
  refine applyArgs_heq (congrArg (List.map _) hins.symm) (by rw [hout']) ?_
    (denoteArgs_heq_tys hins.symm _ _)
  show HEq (op g.name.name _) (op (demangleName g'.name.name) _)
  rw [hname]
  exact opInterp_heq op _ (by rw [hout', hins])

/-- An instance of a function has the function's concrete evaluator. -/
private theorem FnInstance.concreteEval_eq {g g' : LFunc T} (hrel : FnInstance g g') :
    g'.concreteEval = g.concreteEval := by
  obtain ⟨_, _, -, -, -, -, -, h, -⟩ := hrel
  exact h

/-- Demangling is a renaming every concrete evaluator of `F` commutes with. -/
@[expose] def ConcreteEvalsCommuteDemangle (F : Lambda.Factory T) : Prop :=
  ∀ o (ho : o ∈ F), ∀ c, (F[o]'ho).concreteEval = some c → ∀ md args res, c md args = some res →
    c md (args.map (·.renameOps demangleRen)) = some (res.renameOps demangleRen)

/-- **A model of a factory of instances.** If every function of `F'` is an instance of a
    function of `F`, `F`'s concrete evaluators commute with demangling, and every
    constructor of `F'` is a constructor of `F` with a name that demangles to itself, then
    reading every operator `n` as a model of `F` reads `demangleName n` is a model of `F'`,
    with the same carriers. -/
@[expose] noncomputable def Interp.ofInstances [DecidableEq T.IDMeta] {F F' : Lambda.Factory T}
    (I : Interp F)
    (hrel : ∀ n (hn : n ∈ F'), ∃ o, ∃ ho : o ∈ F, FnInstance (F[o]'ho) (F'[n]'hn))
    (hnat : ConcreteEvalsCommuteDemangle F)
    (hconstr : ∀ f' ∈ F'.toArray, f'.isConstr = true →
      f' ∈ F.toArray ∧ demangleName f'.name.name = f'.name.name) : Interp F' where
  tcInterp := I.tcInterp
  opInterp := demangledOpInterp I.opInterp
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
    refine ⟨fun f1 f2 h1 h2 c1 c2 hne vt => ?_, fun f h c vt => ?_⟩
    · have hold := I.constrConsistent.constr_disjoint f1 f2 (hconstr f1 h1 c1).1
        (hconstr f2 h2 c2).1 c1 c2 hne vt
      unfold demangledOpInterp
      rw [(hconstr f1 h1 c1).2, (hconstr f2 h2 c2).2]
      exact hold
    · have hold := I.constrConsistent.constr_injective f (hconstr f h c).1 c vt
      unfold demangledOpInterp
      rw [(hconstr f h c).2]
      exact hold

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
    | some ts => ⟨mangledName o.name ts.givenTypes, ()⟩
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
theorem applyOnceDFSM_rewriteLExprOp (P : PolymorphicFuncDecls)
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
theorem mangleOpsInLExpr_run (P : PolymorphicFuncDecls) (F : Lambda.Factory CoreLParams)
    (e : Expression.Expr) (c : PtrCache mangleTy) :
    ∃ c', (mangleOpsInLExpr P F e).run c = (e.renameOps (monoRen P F), c') := by
  obtain ⟨w, c', h⟩ := applyOnceDFSM_rewriteLExprOp P F e c
  refine ⟨c', ?_⟩
  simp only [StateT.run] at h
  simp only [mangleOpsInLExpr, StateT.run, bind, StateT.bind, h, pure, StateT.pure]


end Core.MonomorphizeFunctions
