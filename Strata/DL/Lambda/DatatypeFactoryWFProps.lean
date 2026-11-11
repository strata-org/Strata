/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.TypeFactoryProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.TypeFactoryProps
import all Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.LExprProps
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.NamePrefixesProps

/-! ## Functions generated for mutual datatypes: well-formedness and signatures

Key theorems: `genBlockFactory_wf` (every function generated for a block is
well formed when the block passes validation and the check that its constructor
fields use only the datatype's type parameters), `mem_genBlockFactory` (each
generated function is an eliminator, constructor, tester, destructor or unsafe
destructor of the block) and `genBlockFactory_sigs_of` (a property of types
that type variables, `bool`, the block's datatypes and its constructor argument
types have, and that arrows build and split, holds for every generated
signature type); `genBlockFactory_sigsAllowed` is its instance for names
without a reserved prefix. `genBlockFactory_names` says the generated factory
holds exactly the functions named by `generatedFuncNames`, in that order.

`datatypeGetConstr_eraseMetadata_congr` and `elimConcreteEval_eraseMetadata`
say constructor recognition and the eliminator's evaluator ignore metadata;
`datatypeGetConstr_getVars` and `elimConcreteEval_getVars` say they introduce
no variables beyond those of their inputs.
`LContext.addMutualBlock_genBlockFactory_wf` says that for a block a context
accepts, `genBlockFactory` succeeds and every function it generates is well
formed.

These facts are kept apart from `TypeFactoryProps` so that `TypeFactoryProps`
does not import function well-formedness, the name-prefix facts and the facts
about evaluation. -/

namespace Lambda

open Std (ToFormat)
open Strata.DL.Util (TyIdentifier)

public section

/-- A factory generated for a mutual block is the default factory of an empty
    block, or the result of adding the block's generated functions to the
    default factory one at a time. -/
private theorem genBlockFactory_ok_inv {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    (hgen : genBlockFactory block = .ok fac) :
    (block = [] ∧ fac = Factory.default) ∨
    List.foldlM (fun F fn => Factory.tryPush F fn) Factory.default
      (elimFuncs block default
        ++ block.flatMap (fun d => d.constrs.map (fun c => constrFunc c d))
        ++ block.flatMap (fun d =>
          d.constrs.map (fun c => testerFunc block d c default))
        ++ block.flatMap (fun d =>
          d.constrs.flatMap (fun c => destructorFuncs d c))
        ++ block.flatMap (fun d =>
          d.constrs.flatMap (fun c => unsafeDestructorFuncs d c)))
      = .ok fac := by
  simp only [genBlockFactory] at hgen
  split at hgen
  · rename_i hempty
    simp only [pure, Except.pure, Except.ok.injEq] at hgen
    exact .inl ⟨List.isEmpty_iff.mp hempty, hgen.symm⟩
  · simp only [Factory.tryAddAll] at hgen
    rw [← Array.foldlM_toList] at hgen
    exact .inr hgen

/-- Every function in the factory a mutual block generates is one of the
    block's eliminators, or, for some constructor of a datatype of the block,
    its constructor function, its tester, or one of its destructors or unsafe
    destructors. -/
theorem mem_genBlockFactory {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    {block : MutualDatatype T.IDMeta} {fac : Factory T}
    (hgen : genBlockFactory block = .ok fac) {f : LFunc T}
    (hf : f ∈ fac.toArray) :
    f ∈ elimFuncs block default ∨
      (∃ d ∈ block, ∃ c ∈ d.constrs, f = constrFunc c d) ∨
      (∃ d ∈ block, ∃ c ∈ d.constrs, f = testerFunc block d c default) ∨
      (∃ d ∈ block, ∃ c ∈ d.constrs, f ∈ destructorFuncs d c) ∨
      (∃ d ∈ block, ∃ c ∈ d.constrs, f ∈ unsafeDestructorFuncs d c) := by
  rcases genBlockFactory_ok_inv block fac hgen with ⟨-, rfl⟩ | hgen
  · exact absurd hf (by simp [Lambda.Factory.default])
  rcases Factory.mem_foldlM_tryPush _ _ fac hgen f hf with hdef | hlist
  · exact absurd hdef (by simp [Lambda.Factory.default])
  simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hlist
  rcases hlist with
    (((helim | ⟨d, hd, c, hc, hcf⟩) | ⟨d, hd, c, hc, hcf⟩) |
      ⟨d, hd, c, hc, hcf⟩) | ⟨d, hd, c, hc, hcf⟩
  · exact .inl helim
  · exact .inr (.inl ⟨d, hd, c, hc, hcf.symm⟩)
  · exact .inr (.inr (.inl ⟨d, hd, c, hc, hcf.symm⟩))
  · exact .inr (.inr (.inr (.inl ⟨d, hd, c, hc, hcf⟩)))
  · exact .inr (.inr (.inr (.inr ⟨d, hd, c, hc, hcf⟩)))

/-- The factory a mutual block generates holds exactly the functions named by
    `MutualDatatype.generatedFuncNames`, in that order. -/
theorem genBlockFactory_names {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    {block : MutualDatatype T.IDMeta} {fac : Factory T}
    (hgen : genBlockFactory block = .ok fac) :
    fac.toArray.toList.map (·.name.name) = block.generatedFuncNames := by
  rcases genBlockFactory_ok_inv block fac hgen with ⟨rfl, rfl⟩ | hgen
  · rfl
  rw [Factory.toList_toArray_foldlM_tryPush _ _ fac hgen]
  simp only [Lambda.Factory.default, List.nil_append, List.map_append,
    elimFuncs_names, List.map_flatMap, List.map_map, Function.comp_def,
    destructorFuncs_names, unsafeDestructorFuncs_names,
    MutualDatatype.generatedFuncNames]
  rfl

/-- A constructor's field names are distinct whenever the block's factory could
    be built. -/
private theorem genBlockFactory_constr_args_nodup {T : LExprParams}
    [Inhabited T.Metadata] [Inhabited T.IDMeta] [ToFormat T.IDMeta]
    [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    (hgen : genBlockFactory block = .ok fac) :
    ∀ d ∈ block, ∀ c ∈ d.constrs,
      List.Nodup (c.args.map (fun p => p.1.name)) := by
  intro d hd c hc
  rcases genBlockFactory_ok_inv block fac hgen with ⟨rfl, -⟩ | hgen
  · exact absurd hd List.not_mem_nil
  have hnodup := foldlM_tryPush_names_nodup _ _ _ hgen
  simp only [List.map_append] at hnodup
  have h1 := (List.nodup_append.mp hnodup).1
  have h4 := (List.nodup_append.mp h1).2.1
  have houter := List.sublist_flatMap_of_mem
    (fun e : LDatatype T.IDMeta =>
      e.constrs.flatMap (fun c => destructorFuncs (T := T) e c))
    block d hd
  have hinner := List.sublist_flatMap_of_mem
    (fun c : LConstr T.IDMeta => destructorFuncs (T := T) d c) d.constrs c hc
  have hsub := hinner.trans houter
  have hdc :
      List.Nodup ((destructorFuncs (T := T) d c).map (fun f => f.name.name)) :=
    List.Nodup.sublist (hsub.map _) h4
  rw [destructorFuncs_names] at hdc
  exact List.nodup_of_nodup_map _ hdc

/-! ### Matching an expression against an operator name -/

/-- An expression whose callee is not an operator reference matches no name. -/
private theorem matchOp_eq_none {T : LExprParams} [BEq T.Identifier]
    (e : LExpr T.mono) (o : T.Identifier)
    (h : ∀ m o' ty, (getLFuncCall e).1 ≠ .op m o' ty) :
    LExpr.matchOp e o = none := by
  simp only [LExpr.matchOp]
  cases hc : getLFuncCall e with | mk op args =>
  rw [hc] at h
  simp only at h
  cases op
  case op m o' ty => exact absurd rfl (h m o' ty)
  all_goals rfl

/-- Matching against a name compares it with the callee's operator, returning
    the callee's arguments on success. -/
private theorem matchOp_eq_of_head {T : LExprParams} [BEq T.Identifier]
    (e : LExpr T.mono) (o : T.Identifier) (m : T.Metadata) (o₁ : T.Identifier)
    (ty : Option LMonoTy)
    (h : (getLFuncCall e).1 = .op m o₁ ty) :
    LExpr.matchOp e o = if o == o₁ then some (getLFuncCall e).2 else none := by
  simp only [LExpr.matchOp]
  cases hc : getLFuncCall e with | mk op args =>
  rw [hc] at h
  simp only at h
  subst h
  simp only

/-- Every free variable of an argument that `getLFuncCall.go` collects is a free
    variable of the scanned expression or of an argument already collected. -/
private theorem getLFuncCall_go_getVars_mem {T : LExprParams}
    (e : LExpr T.mono) (acc : List (LExpr T.mono))
    (op : LExpr T.mono) (args : List (LExpr T.mono))
    (h : getLFuncCall.go e acc = (op, args))
    (a : LExpr T.mono) (ha : a ∈ args)
    (y : T.Identifier) (hy : y ∈ LExpr.LExpr.getVars a) :
    y ∈ LExpr.LExpr.getVars e ∨ ∃ b ∈ acc, y ∈ LExpr.LExpr.getVars b := by
  revert op args
  fun_induction getLFuncCall.go e acc with
  | case1 acc m m' e' arg1 arg2 ih =>
    intro op args h ha
    have hrec := ih op args h ha
    simp only [LExpr.LExpr.getVars, List.mem_append, List.cons_append,
      List.nil_append] at hrec ⊢
    grind
  | case2 acc m m' fn fnty arg1 =>
    intro op args h ha
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | hmem
    · simp only [LExpr.LExpr.getVars, List.mem_append]
      exact .inl (.inr hy)
    · exact .inr ⟨a, hmem, hy⟩
  | case3 e acc =>
    intro op args h ha
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .inr ⟨a, ha, hy⟩

/-- On a successful match the arguments handed back are the callee's
    arguments. -/
private theorem matchOp_args {T : LExprParams} [BEq T.Identifier]
    (e : LExpr T.mono) (o : T.Identifier) (args : List (LExpr T.mono))
    (h : LExpr.matchOp e o = some args) :
    (getLFuncCall e).2 = args := by
  simp only [LExpr.matchOp] at h
  cases hc : getLFuncCall e with | mk op as =>
  rw [hc] at h
  show as = args
  cases op
  case op m o₁ ty =>
    simp only at h
    elim_err h
    simpa only [Option.some.injEq] using h
  all_goals exact absurd h (by simp)

/-- An operator match returns arguments with no variables beyond the matched
    expression's. -/
private theorem matchOp_getVars {T : LExprParams} [BEq T.Identifier]
    (e : LExpr T.mono) (o : T.Identifier) (args : List (LExpr T.mono))
    (h : LExpr.matchOp e o = some args)
    (a : LExpr T.mono) (ha : a ∈ args) (y : T.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars a) : y ∈ LExpr.LExpr.getVars e := by
  have hget : getLFuncCall.go e [] = ((getLFuncCall e).1, args) := by
    show getLFuncCall e = _
    rw [← matchOp_args e o args h]
  rcases getLFuncCall_go_getVars_mem e [] _ args hget a ha y hy with
    h1 | ⟨b, hb, _⟩
  · exact h1
  · exact absurd hb (by simp)

/-- Expressions differing only in metadata match the same operator names, with
    arguments differing only in metadata. -/
private theorem matchOp_eraseMetadata_congr {T : LExprParams} [BEq T.Identifier]
    (e₁ e₂ : LExpr T.mono) (o : T.Identifier)
    (h : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.matchOp e₁ o = none ∧ LExpr.matchOp e₂ o = none) ∨
    (∃ a₁ a₂, LExpr.matchOp e₁ o = some a₁ ∧ LExpr.matchOp e₂ o = some a₂ ∧
      a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata) := by
  obtain ⟨hop, hargs⟩ := getLFuncCall_eraseMetadata_congr e₁ e₂ h
  rcases eraseMetadata_op_cases (getLFuncCall e₁).1 (getLFuncCall e₂).1 hop with
    ⟨m₁, m₂, oo, ty, hA, hB⟩ | ⟨hA, hB⟩
  · rw [matchOp_eq_of_head e₁ o m₁ oo ty hA,
      matchOp_eq_of_head e₂ o m₂ oo ty hB]
    split
    · exact Or.inr ⟨_, _, rfl, rfl, hargs⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨matchOp_eq_none e₁ o hA, matchOp_eq_none e₂ o hB⟩

/-! ### Recognizing which constructor built a value -/

/-- Scanning a constructor list for a match is insensitive to metadata. -/
private theorem foldr_matchOp_eraseMetadata_congr {T : LExprParams}
    [BEq T.Identifier] (x₁ x₂ : LExpr T.mono)
    (h : x₁.eraseMetadata = x₂.eraseMetadata)
    (l : List (LConstr T.IDMeta × Nat)) :
    (List.foldr (fun (c, i) acc =>
        match LExpr.matchOp x₁ c.name with
        | .some args => .some (c, i, args)
        | .none => acc) .none l = none ∧
      List.foldr (fun (c, i) acc =>
        match LExpr.matchOp x₂ c.name with
        | .some args => .some (c, i, args)
        | .none => acc) .none l = none) ∨
    (∃ c i a₁ a₂,
      List.foldr (fun (c, i) acc =>
        match LExpr.matchOp x₁ c.name with
        | .some args => .some (c, i, args)
        | .none => acc) .none l = some (c, i, a₁) ∧
      List.foldr (fun (c, i) acc =>
        match LExpr.matchOp x₂ c.name with
        | .some args => .some (c, i, args)
        | .none => acc) .none l = some (c, i, a₂) ∧
      a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata) := by
  induction l with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨c, i⟩ := p
    rcases matchOp_eraseMetadata_congr x₁ x₂ c.name h with
      ⟨h1, h2⟩ | ⟨a₁, a₂, h1, h2, ha⟩
    · simpa only [List.foldr_cons, h1, h2] using ih
    · simp only [List.foldr_cons, h1, h2]
      exact Or.inr ⟨c, i, a₁, a₂, rfl, rfl, ha⟩

/-- Constructor recognition is insensitive to metadata: values differing only in
    metadata give the same constructor and position, with arguments differing
    only in metadata. -/
theorem datatypeGetConstr_eraseMetadata_congr {T : LExprParams}
    [BEq T.Identifier] (d : LDatatype T.IDMeta) (x₁ x₂ : LExpr T.mono)
    (h : x₁.eraseMetadata = x₂.eraseMetadata) :
    (datatypeGetConstr (T := T) d x₁ = none ∧
      datatypeGetConstr (T := T) d x₂ = none) ∨
    (∃ c i a₁ a₂, datatypeGetConstr (T := T) d x₁ = some (c, i, a₁) ∧
      datatypeGetConstr (T := T) d x₂ = some (c, i, a₂) ∧
      a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata) := by
  simp only [datatypeGetConstr]
  exact foldr_matchOp_eraseMetadata_congr x₁ x₂ h _

/-- Scanning a constructor list hands back arguments with no variables beyond
    the scanned expression's. -/
private theorem foldr_matchOp_getVars {T : LExprParams} [BEq T.Identifier]
    (x : LExpr T.mono)
    (l : List (LConstr T.IDMeta × Nat)) :
    ∀ c i a, List.foldr (fun (c, i) acc =>
        match LExpr.matchOp x c.name with
        | .some args => .some (c, i, args)
        | .none => acc) .none l = some (c, i, a) →
      ∀ b ∈ a, ∀ y ∈ LExpr.LExpr.getVars b, y ∈ LExpr.LExpr.getVars x := by
  induction l with
  | nil => intro c i a hfold; exact absurd hfold (by simp)
  | cons p rest ih =>
    obtain ⟨c₀, i₀⟩ := p
    intro c i a hfold b hb y hy
    simp only [List.foldr_cons] at hfold
    cases hm : LExpr.matchOp x c₀.name with
    | none => rw [hm] at hfold; exact ih c i a hfold b hb y hy
    | some args =>
      rw [hm] at hfold
      simp only [Option.some.injEq, Prod.mk.injEq] at hfold
      obtain ⟨-, -, haEq⟩ := hfold
      exact matchOp_getVars x c₀.name args hm b (haEq ▸ hb) y hy

/-- The arguments of a recognized constructor application have no variables
    beyond its own. -/
theorem datatypeGetConstr_getVars {T : LExprParams} [BEq T.Identifier]
    (d : LDatatype T.IDMeta) (x : LExpr T.mono) (c : LConstr T.IDMeta) (i : Nat)
    (a : List (LExpr T.mono))
    (h : datatypeGetConstr (T := T) d x = some (c, i, a))
    (b : LExpr T.mono) (hb : b ∈ a) (y : T.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars b) : y ∈ LExpr.LExpr.getVars x := by
  simp only [datatypeGetConstr] at h
  exact foldr_matchOp_getVars x _ c i a h b hb y hy

/-! ### The eliminator's recursive calls -/

/-- Bound-variable references have no free variables. -/
private theorem getVars_getBVars {T : LExprParams} (m : T.Metadata) (n : Nat) :
    ∀ b ∈ getBVars (T := T) m n, LExpr.LExpr.getVars b = [] := by
  intro b hb
  simp only [getBVars, List.mem_map] at hb
  obtain ⟨i, _, hib⟩ := hb
  rw [← hib]
  rfl

/-- Building the eliminator's recursive call is insensitive to metadata: inputs
    differing only in metadata give no call in both cases or calls differing
    only in metadata. -/
private theorem elimRecCall_eraseMetadata_congr {T : LExprParams}
    [Inhabited T.IDMeta]
    (block : MutualDatatype T.IDMeta) (r₁ r₂ : LExpr T.mono) (rty : LMonoTy)
    (xs₁ xs₂ : List (LExpr T.mono)) (m : T.Metadata)
    (hr : r₁.eraseMetadata = r₂.eraseMetadata)
    (hxs : xs₁.map LExpr.eraseMetadata = xs₂.map LExpr.eraseMetadata) :
    (elimRecCall block r₁ rty xs₁ m = none ∧
      elimRecCall block r₂ rty xs₂ m = none) ∨
    (∃ e₁ e₂, elimRecCall block r₁ rty xs₁ m = some e₁ ∧
      elimRecCall block r₂ rty xs₂ m = some e₂ ∧
      e₁.eraseMetadata = e₂.eraseMetadata) := by
  simp only [elimRecCall]
  cases hf : findRecTy block rty with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some d =>
    simp only [Option.map_some]
    refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
    cases hrs : recTyStructure d rty with
    | inl u =>
      simp only [LExpr.eraseMetadata_mkApp, List.map_cons, hr, hxs]
    | inr funArgs =>
      simp only [eraseMetadata_absMulti, LExpr.eraseMetadata_mkApp,
        List.map_cons, hr, hxs]

/-- The eliminator's recursive call introduces no variables beyond those of the
    recursive argument and of the case functions. -/
private theorem getVars_elimRecCall {T : LExprParams} [Inhabited T.IDMeta]
    (block : MutualDatatype T.IDMeta) (recArg : LExpr T.mono) (rty : LMonoTy)
    (xs : List (LExpr T.mono)) (m : T.Metadata) (res : LExpr T.mono)
    (h : elimRecCall block recArg rty xs m = some res) :
    ∀ y ∈ LExpr.LExpr.getVars res,
      y ∈ LExpr.LExpr.getVars recArg ∨ ∃ b ∈ xs, y ∈ LExpr.LExpr.getVars b := by
  simp only [elimRecCall] at h
  cases hf : findRecTy block rty with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some d =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    cases hrs : recTyStructure d rty with
    | inl u =>
      intro y hy
      rcases getVars_mkApp m _ _ y hy with hop | ⟨b, hb, hby⟩
      · exact absurd hop (by simp [LExpr.LExpr.getVars])
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl hby
        · exact Or.inr ⟨b, hb', hby⟩
    | inr funArgs =>
      intro y hy
      simp only [getVars_absMulti] at hy
      rcases getVars_mkApp m _ _ y hy with hop | ⟨b, hb, hby⟩
      · exact absurd hop (by simp [LExpr.LExpr.getVars])
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rcases getVars_mkApp m recArg _ y hby with h1 | ⟨cb, hcb, hcby⟩
          · exact Or.inl h1
          · change cb ∈ getBVars m funArgs.length at hcb
            rw [getVars_getBVars m funArgs.length cb hcb] at hcby
            exact absurd hcby (by simp)
        · exact Or.inr ⟨b, hb', hby⟩

/-! ### Recognizing which constructor of the block built a value -/

/-- Argument lists differing only in metadata have recursive arguments, selected
    by type, that differ only in metadata. -/
private theorem forall₂_recs {T : LExprParams} (block : MutualDatatype T.IDMeta)
    (a₁ a₂ : List (LExpr T.mono)) (tys : List LMonoTy)
    (h : a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata) :
    List.Rel₂
      (fun q r => LExpr.eraseMetadata q.1 = LExpr.eraseMetadata r.1 ∧ q.2 = r.2)
      ((a₁.zip tys).filter (fun q => isRecTy block q.2))
      ((a₂.zip tys).filter (fun q => isRecTy block q.2)) :=
  List.forall₂_filter_zip _ (fun ty => isRecTy block ty) a₁ a₂
    ((forall₂_iff_map_eraseMetadata_eq a₁ a₂).mpr h) tys

/-- Block constructor recognition is insensitive to metadata: values differing
    only in metadata give the same constructor, with arguments differing only
    in metadata. -/
private theorem matchConstr_eraseMetadata_congr {T : LExprParams}
    [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (x₁ x₂ : LExpr T.mono)
    (h : x₁.eraseMetadata = x₂.eraseMetadata) :
    (matchConstr block x₁ = none ∧ matchConstr block x₂ = none) ∨
    (∃ dtIdx constrIdx c a₁ a₂ r₁ r₂,
      matchConstr block x₁ = some (dtIdx, constrIdx, c, a₁, r₁) ∧
      matchConstr block x₂ = some (dtIdx, constrIdx, c, a₂, r₂) ∧
      a₁.map LExpr.eraseMetadata = a₂.map LExpr.eraseMetadata ∧
      List.Rel₂
        (fun q r => LExpr.eraseMetadata q.1 = LExpr.eraseMetadata r.1 ∧
          q.2 = r.2)
        r₁ r₂) := by
  have hpacked :
      (matchConstr block x₁ = none ∧ matchConstr block x₂ = none) ∨
      (∃ t₁ t₂, matchConstr block x₁ = some t₁ ∧
        matchConstr block x₂ = some t₂ ∧
        (t₁.1 = t₂.1 ∧ t₁.2.1 = t₂.2.1 ∧ t₁.2.2.1 = t₂.2.2.1 ∧
          t₁.2.2.2.1.map LExpr.eraseMetadata =
            t₂.2.2.2.1.map LExpr.eraseMetadata ∧
          List.Rel₂ (fun (s t : LExpr T.mono × LMonoTy) =>
            LExpr.eraseMetadata s.1 = LExpr.eraseMetadata t.1 ∧ s.2 = t.2)
            t₁.2.2.2.2 t₂.2.2.2.2)) := by
    simp only [matchConstr]
    refine List.findSome?_congr
      (fun (p q : Nat × Nat × LConstr T.IDMeta × List (LExpr T.mono) ×
          List (LExpr T.mono × LMonoTy)) =>
        p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧
        p.2.2.2.1.map LExpr.eraseMetadata = q.2.2.2.1.map LExpr.eraseMetadata ∧
        List.Rel₂ (fun (s t : LExpr T.mono × LMonoTy) =>
          LExpr.eraseMetadata s.1 = LExpr.eraseMetadata t.1 ∧ s.2 = t.2)
          p.2.2.2.2 q.2.2.2.2) _ _ _ ?_
    intro p _
    obtain ⟨d, dtIdx⟩ := p
    rcases datatypeGetConstr_eraseMetadata_congr d x₁ x₂ h with
      ⟨hn1, hn2⟩ | ⟨c, i, b₁, b₂, hs1, hs2, hb⟩
    · exact Or.inl ⟨by simp only [hn1, Option.map_none],
        by simp only [hn2, Option.map_none]⟩
    · refine Or.inr ⟨(dtIdx, i, c, b₁, (b₁.zip (c.args.map Prod.snd)).filter
          (fun q => isRecTy block q.2)),
        (dtIdx, i, c, b₂, (b₂.zip (c.args.map Prod.snd)).filter
          (fun q => isRecTy block q.2)),
        by simp only [hs1, Option.map_some],
        by simp only [hs2, Option.map_some],
        rfl, rfl, rfl, hb, forall₂_recs block b₁ b₂ (c.args.map Prod.snd) hb⟩
  rcases hpacked with
    ⟨hn1, hn2⟩ | ⟨t₁, t₂, hp, hq, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨hn1, hn2⟩
  obtain ⟨dtIdx, constrIdx, c, a₁, r₁⟩ := t₁
  obtain ⟨dtIdx', constrIdx', c', a₂, r₂⟩ := t₂
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3
  exact Or.inr ⟨dtIdx, constrIdx, c, a₁, a₂, r₁, r₂, hp, hq, h4, h5⟩

/-- The arguments and recursive arguments a constructor match returns have no
    variables beyond the matched value's. -/
private theorem matchConstr_getVars {T : LExprParams} [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (x : LExpr T.mono)
    (dtIdx constrIdx : Nat) (c : LConstr T.IDMeta) (a : List (LExpr T.mono))
    (recs : List (LExpr T.mono × LMonoTy))
    (h : matchConstr block x = some (dtIdx, constrIdx, c, a, recs)) :
    (∀ b ∈ a, ∀ y ∈ LExpr.LExpr.getVars b, y ∈ LExpr.LExpr.getVars x) ∧
    (∀ p ∈ recs, ∀ y ∈ LExpr.LExpr.getVars p.1, y ∈ LExpr.LExpr.getVars x) := by
  simp only [matchConstr] at h
  refine List.findSome?_prop _
    (fun t =>
      (∀ b ∈ t.2.2.2.1, ∀ y ∈ LExpr.LExpr.getVars b,
        y ∈ LExpr.LExpr.getVars x) ∧
      (∀ p ∈ t.2.2.2.2, ∀ y ∈ LExpr.LExpr.getVars p.1,
        y ∈ LExpr.LExpr.getVars x)) _ ?_ _ h
  intro p _ t ht
  obtain ⟨d, dtIdx'⟩ := p
  simp only [Option.map_eq_some_iff] at ht
  obtain ⟨v, hv, htEq⟩ := ht
  obtain ⟨c', i', b⟩ := v
  subst htEq
  have hargs :
      ∀ e ∈ b, ∀ y ∈ LExpr.LExpr.getVars e, y ∈ LExpr.LExpr.getVars x :=
    fun e he y hy => datatypeGetConstr_getVars d x c' i' b hv e he y hy
  refine ⟨hargs, ?_⟩
  intro q hq y hy
  have hzip : (q.1, q.2) ∈ b.zip (c'.args.map Prod.snd) :=
    (List.mem_filter.mp hq).1
  exact hargs q.1 (List.of_mem_zip hzip).1 y hy

/-! ### The eliminator's evaluator -/

/-- The eliminator's evaluator succeeds only on a scrutinee together with one
    case function per constructor of the block. -/
private theorem elimConcreteEval_length {T : LExprParams} [BEq T.Identifier]
    [Inhabited T.IDMeta] (block : MutualDatatype T.IDMeta) (m md : T.Metadata)
    (opTy : Option LMonoTy) (args : List (LExpr T.mono))
    (res : LExpr T.mono) (h : elimConcreteEval block m md opTy args = some res) :
    args.length = blockConstrCount block + 1 := by
  simp only [elimConcreteEval] at h
  elim_err h with hlen
  simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using hlen

/-- The eliminator's evaluator is insensitive to metadata: if it succeeds on an
    argument list, it succeeds on any list differing only in metadata, with a
    result differing only in metadata. -/
theorem elimConcreteEval_eraseMetadata {T : LExprParams} [BEq T.Identifier]
    [Inhabited T.IDMeta] (block : MutualDatatype T.IDMeta)
    (m md1 md2 : T.Metadata) (opTy : Option LMonoTy)
    (args1 args2 : List (LExpr T.mono)) (res1 : LExpr T.mono)
    (hmap : args1.map LExpr.eraseMetadata = args2.map LExpr.eraseMetadata)
    (h : elimConcreteEval block m md1 opTy args1 = some res1) :
    ∃ res2, elimConcreteEval block m md2 opTy args2 = some res2 ∧
      LExpr.eraseMetadata res1 = LExpr.eraseMetadata res2 := by
  have hlen : args1.length = args2.length := by
    have h_len := congrArg List.length hmap
    simpa only [List.length_map] using h_len
  simp only [elimConcreteEval] at h ⊢
  elim_err h with hguard
  rw [hlen] at hguard
  rw [ite_eq_right hguard]
  cases args1 with
  | nil => exact absurd h (by simp)
  | cons x1 xs1 =>
    cases args2 with
    | nil => exact absurd hmap (by simp)
    | cons x2 xs2 =>
      rw [List.map_cons, List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hx, hxs⟩ := hmap
      simp only at h ⊢
      rcases matchConstr_eraseMetadata_congr block x1 x2 hx with
        ⟨hn1, hn2⟩ | ⟨dtIdx, constrIdx, c, a₁, a₂, r₁, r₂, hm1, hm2, ha, hr⟩
      · rw [hn1] at h; exact absurd h (by simp)
      rw [hm1] at h
      rw [hm2]
      simp only at h ⊢
      cases hf1 : xs1[blockConstrIdx block dtIdx constrIdx]? with
      | none => rw [hf1] at h; exact absurd h (by simp)
      | some f1 =>
        rw [hf1, Option.bind_some, Option.some.injEq] at h
        obtain ⟨f2, hf2, hfe⟩ :=
          getElem?_of_map_eraseMetadata_eq xs1 xs2 hxs _ f1 hf1
        rw [hf2, Option.bind_some]
        refine ⟨_, rfl, ?_⟩
        have hrec : List.Rel₂
            (fun p q => LExpr.eraseMetadata p = LExpr.eraseMetadata q)
            (r₁.filterMap (fun q => elimRecCall block q.1 q.2 xs1 m))
            (r₂.filterMap (fun q => elimRecCall block q.1 q.2 xs2 m)) := by
          refine List.forall₂_filterMap _ _ _ _ ?_ r₁ r₂ hr
          intro p q hpq
          rw [← hpq.2]
          exact elimRecCall_eraseMetadata_congr block p.1 q.1 p.2 xs1 xs2 m
            hpq.1 hxs
        have hargs :
            (a₁ ++ r₁.filterMap (fun q => elimRecCall block q.1 q.2 xs1 m)).map
              LExpr.eraseMetadata =
            (a₂ ++ r₂.filterMap (fun q => elimRecCall block q.1 q.2 xs2 m)).map
              LExpr.eraseMetadata := by
          rw [List.map_append, List.map_append, ha,
            (forall₂_iff_map_eraseMetadata_eq _ _).mp hrec]
        rw [← h, LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp, hfe,
          hargs]

/-- Every variable of the eliminator evaluator's result is a variable of some
    argument. -/
theorem elimConcreteEval_getVars {T : LExprParams} [BEq T.Identifier]
    [Inhabited T.IDMeta] (block : MutualDatatype T.IDMeta) (m md : T.Metadata)
    (opTy : Option LMonoTy) (args : List (LExpr T.mono))
    (res : LExpr T.mono) (h : elimConcreteEval block m md opTy args = some res) :
    ∀ z ∈ LExpr.LExpr.getVars res, ∃ a ∈ args, z ∈ LExpr.LExpr.getVars a := by
  simp only [elimConcreteEval] at h
  elim_err h
  cases args with
  | nil => exact absurd h (by simp)
  | cons x xs =>
    simp only at h
    cases hmc : matchConstr block x with
    | none => rw [hmc] at h; exact absurd h (by simp)
    | some v =>
      obtain ⟨dtIdx, constrIdx, c, a, recs⟩ := v
      rw [hmc] at h
      simp only at h
      cases hf : xs[blockConstrIdx block dtIdx constrIdx]? with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some f =>
        rw [hf, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨hargs, hrecs⟩ :=
          matchConstr_getVars block x dtIdx constrIdx c a recs hmc
        have hxs : ∀ b ∈ xs, ∀ z ∈ LExpr.LExpr.getVars b,
            ∃ e ∈ x :: xs, z ∈ LExpr.LExpr.getVars e :=
          fun b hb z hz => ⟨b, List.mem_cons_of_mem x hb, hz⟩
        intro z hz
        rcases getVars_mkApp m f _ z hz with hfz | ⟨b, hb, hbz⟩
        · exact hxs f (List.mem_of_getElem? hf) z hfz
        rcases List.mem_append.mp hb with hb_a | hb_rec
        · exact ⟨x, List.mem_cons_self, hargs b hb_a z hbz⟩
        obtain ⟨p, hp, hcall⟩ := List.mem_filterMap.mp hb_rec
        rcases getVars_elimRecCall block p.1 p.2 xs m b hcall z hbz with
          hrz | ⟨e, he, hez⟩
        · exact ⟨x, List.mem_cons_self, hrecs p hp z hrz⟩
        · exact hxs e he z hez

/-! ### Constructors and testers -/

/-- The function generated for a datatype constructor is well formed when the
    constructor's field names are distinct, the datatype's type parameters are
    distinct and none of them starts with `genTyPrefix`, and every field type
    uses only those parameters. -/
private theorem constrFunc_wf {T : LExprParams} (d : LDatatype T.IDMeta)
    (c : LConstr T.IDMeta)
    (hnames : List.Nodup (c.args.map (fun p => p.1.name)))
    (hnodup : d.typeArgs.Nodup)
    (hscoped : ∀ arg ∈ c.args, ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs)
    (hres : ∀ v ∈ d.typeArgs, genTyPrefix.toList.isPrefixOf v.toList = false) :
    LFuncWF (constrFunc (T := T) c d) where
  arg_nodup := hnames
  typeArgs_nodup := hnodup
  inputs_typevars_in_typeArgs := by
    intro ty hty v hv
    obtain ⟨k, hk⟩ := ListMap.mem_values _ ty hty
    exact hscoped (k, ty) hk v hv
  output_typevars_in_typeArgs := by
    intro v hv
    simpa only [constrFunc, freeVars_dataDefault] using hv
  constr_no_eval := by intro _; exact ⟨rfl, rfl⟩
  typeArgs_no_gen_prefix := fun ta hta => Bool.ne_true_of_eq_false (hres ta hta)
  concreteEval_argmatch := by
    intro fn _ _ _ _ hfn; exact absurd hfn (by simp [constrFunc])
  body_or_concreteEval := by simp [constrFunc]
  concreteEval_eraseMetadata := by
    intro _ h; exact absurd h (by simp [constrFunc])
  concreteEval_freeVars := by intro _ h; exact absurd h (by simp [constrFunc])
  shortCircuit_substFvars := by
    intro _ _ h; exact absurd h (by simp [constrFunc])
  body_freevars := by intro _ hb; exact absurd hb (by simp [constrFunc])
  precond_freevars := by intro _ hp; exact absurd hp (by simp [constrFunc])

/-- A tester body's free variables are among those of the value it tests. -/
private theorem getVars_testerFuncBody {T : LExprParams} [Inhabited T.IDMeta]
    (block : MutualDatatype T.IDMeta) (d : LDatatype T.IDMeta)
    (c : LConstr T.IDMeta)
    (input : LExpr T.mono) (m : T.Metadata) :
    ∀ y ∈ LExpr.LExpr.getVars (testerFuncBody block d c input m),
      y ∈ LExpr.LExpr.getVars input := by
  intro y hy
  simp only [testerFuncBody] at hy
  rcases getVars_mkApp m _ _ y hy with hop | ⟨a, ha, hya⟩
  · simp only [LExpr.LExpr.getVars, List.not_mem_nil] at hop
  · rcases List.mem_cons.mp ha with rfl | hargs
    · exact hya
    · obtain ⟨d', -, hd'⟩ := List.mem_flatMap.mp hargs
      obtain ⟨c1, -, rfl⟩ := List.mem_map.mp hd'
      rw [getVars_absMulti] at hya
      simp only [LExpr.LExpr.getVars, List.not_mem_nil] at hya

/-- The tester generated for a datatype constructor is well formed when the
    datatype's type parameters are distinct and none of them starts with
    `genTyPrefix`. -/
private theorem testerFunc_wf {T : LExprParams} [Inhabited T.IDMeta]
    (block : MutualDatatype T.IDMeta) (d : LDatatype T.IDMeta)
    (c : LConstr T.IDMeta)
    (m : T.Metadata) (hnodup : d.typeArgs.Nodup)
    (hres : ∀ v ∈ d.typeArgs, genTyPrefix.toList.isPrefixOf v.toList = false) :
    LFuncWF (testerFunc (T := T) block d c m) where
  arg_nodup := by simp [testerFunc]
  typeArgs_nodup := hnodup
  inputs_typevars_in_typeArgs := by
    intro ty hty v hv
    simp only [testerFunc, ListMap.values, List.mem_cons] at hty
    rcases hty with rfl | hty
    · simpa only [testerFunc, freeVars_dataDefault] using hv
    · exact absurd hty (by simp)
  output_typevars_in_typeArgs := by
    intro v hv
    exact absurd hv
      (by simp [testerFunc, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars])
  constr_no_eval := by intro hc; exact absurd hc (by simp [testerFunc])
  typeArgs_no_gen_prefix := fun ta hta => Bool.ne_true_of_eq_false (hres ta hta)
  concreteEval_argmatch := by
    intro fn _ _ _ _ hfn; exact absurd hfn (by simp [testerFunc])
  body_or_concreteEval := by simp [testerFunc]
  concreteEval_eraseMetadata := by
    intro _ h; exact absurd h (by simp [testerFunc])
  concreteEval_freeVars := by intro _ h; exact absurd h (by simp [testerFunc])
  shortCircuit_substFvars := by
    intro _ _ h; exact absurd h (by simp [testerFunc])
  body_freevars := by
    intro b hb y hy
    simp only [testerFunc, Option.some.injEq] at hb
    subst hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    have hqvars : q.1 ∈ LExpr.LExpr.getVars
        (testerFuncBody block d c
          (.fvar m genArgName (some (dataDefault d))) m) := by
      rw [getVars_eq_freeVars_idents]
      exact List.mem_map_of_mem hq
    have hqarg := getVars_testerFuncBody block d c _ m q.1 hqvars
    simp only [LExpr.LExpr.getVars, List.mem_singleton] at hqarg
    simp [testerFunc, hqarg]
  precond_freevars := by intro _ hp; exact absurd hp (by simp [testerFunc])

/-! ### Projections -/

/-- The checked or unchecked projection of a constructor field is well formed
    when the datatype's type parameters are distinct and none of them starts
    with `genTyPrefix`, and the field's type uses only those parameters. -/
private theorem mkDestructorFunc_wf {T : LExprParams} [BEq T.Identifier]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] (d : LDatatype T.IDMeta)
    (c : LConstr T.IDMeta) (i : Nat)
    (nm : Identifier T.IDMeta) (ty : LMonoTy) (safe : Bool)
    (hnodup : d.typeArgs.Nodup)
    (houtput : ∀ v ∈ LMonoTy.freeVars ty, v ∈ d.typeArgs)
    (hres : ∀ v ∈ d.typeArgs, genTyPrefix.toList.isPrefixOf v.toList = false) :
    LFuncWF (mkDestructorFunc (T := T) d c i nm ty safe) where
  arg_nodup := by simp [mkDestructorFunc]
  typeArgs_nodup := hnodup
  inputs_typevars_in_typeArgs := by
    intro t ht v hv
    simp only [mkDestructorFunc, ListMap.values, List.mem_cons] at ht
    rcases ht with rfl | ht
    · simpa only [mkDestructorFunc, freeVars_dataDefault] using hv
    · exact absurd ht (by simp)
  output_typevars_in_typeArgs := houtput
  constr_no_eval := by intro hc; exact absurd hc (by simp [mkDestructorFunc])
  typeArgs_no_gen_prefix := fun ta hta => Bool.ne_true_of_eq_false (hres ta hta)
  concreteEval_argmatch := by
    intro fn md _ args res hfn heval
    simp only [mkDestructorFunc, Option.some.injEq] at hfn
    subst hfn
    rcases args with _ | ⟨x, xs⟩
    · exact absurd heval (by simp [destructorConcreteEval])
    rcases xs with _ | ⟨y, ys⟩
    · simp [mkDestructorFunc]
    · exact absurd heval (by simp [destructorConcreteEval])
  body_or_concreteEval := by simp [mkDestructorFunc]
  shortCircuit_substFvars := by
    intro h
    simp [mkDestructorFunc, Strata.DL.Util.FuncAttr.hasShortCircuit] at h
  concreteEval_eraseMetadata := by
    intro ceval hceval md1 md2 _ args1 args2 res1 hmap heval
    simp only [mkDestructorFunc, Option.some.injEq] at hceval
    subst hceval
    rcases args1 with _ | ⟨x1, xs1⟩
    · exact absurd heval (by simp [destructorConcreteEval])
    rcases xs1 with _ | ⟨y1, ys1⟩
    · rcases args2 with _ | ⟨x2, xs2⟩
      · exact absurd hmap (by simp)
      rcases xs2 with _ | ⟨y2, ys2⟩
      · have hx : x1.eraseMetadata = x2.eraseMetadata := by simpa using hmap
        simp only [destructorConcreteEval] at heval ⊢
        rcases datatypeGetConstr_eraseMetadata_congr d x1 x2 hx with
          ⟨hn1, hn2⟩ | ⟨c1, j, a1, a2, hs1, hs2, ha⟩
        · rw [hn1] at heval
          exact absurd heval (by simp)
        rw [hs1] at heval
        rw [hs2]
        simp only [Option.bind_some] at heval ⊢
        elim_err heval with hname
        obtain ⟨r2, hr2, her⟩ :=
          getElem?_of_map_eraseMetadata_eq a1 a2 ha i res1 heval
        rw [ite_eq_left hname, hr2]
        exact ⟨r2, rfl, her⟩
      · exact absurd hmap (by simp)
    · exact absurd heval (by simp [destructorConcreteEval])
  concreteEval_freeVars := by
    intro ceval hceval md _ args res heval z hz
    simp only [mkDestructorFunc, Option.some.injEq] at hceval
    subst hceval
    rcases args with _ | ⟨x, xs⟩
    · exact absurd heval (by simp [destructorConcreteEval])
    rcases xs with _ | ⟨y, ys⟩
    · simp only [destructorConcreteEval] at heval
      cases hg : datatypeGetConstr (T := T) d x with
      | none => rw [hg] at heval; exact absurd heval (by simp)
      | some v =>
        obtain ⟨c1, j, a1⟩ := v
        rw [hg] at heval
        simp only [Option.bind_some] at heval
        elim_err heval
        refine ⟨x, by simp, ?_⟩
        exact datatypeGetConstr_getVars d x c1 j a1 hg res
          (List.mem_of_getElem? heval) z hz
    · exact absurd heval (by simp [destructorConcreteEval])
  body_freevars := by intro _ hb; exact absurd hb (by simp [mkDestructorFunc])
  precond_freevars := by
    intro p hp y hy
    simp only [mkDestructorFunc] at hp
    split at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      simpa [LExpr.freeVars, mkDestructorFunc] using hy
    · exact absurd hp (by simp)

/-- Every projection of a constructor's fields, checked or unchecked, is well
    formed when the datatype's type parameters are distinct and none of them
    starts with `genTyPrefix`, and every field type uses only those
    parameters. -/
private theorem destructorFuncs_wf {T : LExprParams} [BEq T.Identifier]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] (d : LDatatype T.IDMeta)
    (c : LConstr T.IDMeta) (b : Bool)
    (hnodup : d.typeArgs.Nodup)
    (hscoped : ∀ arg ∈ c.args, ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs)
    (hres : ∀ v ∈ d.typeArgs, genTyPrefix.toList.isPrefixOf v.toList = false) :
    ∀ f ∈ (bif b then destructorFuncs (T := T) d c
      else unsafeDestructorFuncs d c),
      LFuncWF f := by
  intro f hf
  cases b <;>
    simp only [Bool.cond_true, Bool.cond_false, destructorFuncs,
      unsafeDestructorFuncs, List.mem_mapIdx] at hf <;>
    obtain ⟨k, hk, hkEq⟩ := hf <;>
    rw [← hkEq] <;>
    exact mkDestructorFunc_wf d c k _ _ _ hnodup
      (hscoped c.args[k] (List.getElem_mem hk)) hres

/-! ### Eliminators -/

/-- One generated eliminator is well formed when the datatype's type parameters
    are distinct, the return-type parameters are distinct, the two lists share
    no name, there is one return-type parameter per datatype of the block and
    the output is one of them, no parameter of either list starts with
    `genTyPrefix`, there is one case per constructor of the block, and each case
    has an in-range datatype index and field types using only the datatype's
    parameters. -/
private theorem elimFunc_wf {T : LExprParams} [Inhabited T.IDMeta]
    [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (m : T.Metadata) (d : LDatatype T.IDMeta)
    (retTyVars : List TyIdentifier) (outputTyVar : TyIdentifier)
    (allConstrs : List (Nat × LConstr T.IDMeta))
    (hownnodup : d.typeArgs.Nodup)
    (hretnodup : retTyVars.Nodup)
    (hdisj : ∀ v ∈ retTyVars, v ∉ d.typeArgs)
    (hretlen : retTyVars.length = block.length)
    (houtmem : outputTyVar ∈ retTyVars)
    (hretgen : ∀ v ∈ retTyVars, genTyPrefix.toList.isPrefixOf v.toList = false)
    (howngen : ∀ v ∈ d.typeArgs, genTyPrefix.toList.isPrefixOf v.toList = false)
    (hcount : allConstrs.length = blockConstrCount block)
    (hslot : ∀ q ∈ allConstrs, q.1 < block.length ∧
      ∀ arg ∈ q.2.args, ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs) :
    LFuncWF (T := T)
      { name := elimFuncName d
        typeArgs := retTyVars ++ d.typeArgs
        inputs := (genArgNames (allConstrs.length + 1)).zip
          (dataDefault d ::
            allConstrs.map (fun q => elimTy block retTyVars q.1 q.2))
        output := .ftvar outputTyVar
        concreteEval := some (elimConcreteEval block m)
        attr := #[.evalIfConstr 0] } := by
  have hlensame :
      (genArgNames (IDMeta := T.IDMeta) (allConstrs.length + 1)).length
        = (dataDefault d :: allConstrs.map
            (fun q => elimTy block retTyVars q.1 q.2)).length := by
    rw [genArgNames_length, List.length_cons, List.length_map]
  have hinput : ∀ ty ∈ dataDefault d ::
        allConstrs.map (fun q => elimTy block retTyVars q.1 q.2),
      ∀ v ∈ LMonoTy.freeVars ty, v ∈ retTyVars ++ d.typeArgs := by
    intro ty hty v hv
    rcases List.mem_cons.mp hty with rfl | hcase
    · exact List.mem_append_right _
        (by simpa only [freeVars_dataDefault] using hv)
    obtain ⟨q, hq, hqty⟩ := List.mem_map.mp hcase
    obtain ⟨hlt, hqargs⟩ := hslot q hq
    refine freeVars_elimTy_subset block retTyVars q.1 q.2 _
      (fun w hw => List.mem_append_left _ hw) (hretlen ▸ hlt) ?_ v (hqty ▸ hv)
    intro arg harg w hw
    exact List.mem_append_right _ (hqargs arg harg w hw)
  refine
    { arg_nodup := ?_
      typeArgs_nodup := ?_
      inputs_typevars_in_typeArgs := ?_
      output_typevars_in_typeArgs := ?_
      body_freevars := ?_
      precond_freevars := ?_
      constr_no_eval := ?_
      typeArgs_no_gen_prefix := ?_
      concreteEval_argmatch := ?_
      body_or_concreteEval := ?_
      concreteEval_eraseMetadata := ?_
      concreteEval_freeVars := ?_ }
  · show List.Nodup
      (List.map (fun q : Identifier T.IDMeta × LMonoTy => q.1.name)
        ((genArgNames (allConstrs.length + 1)).zip
          (dataDefault d ::
            allConstrs.map (fun q => elimTy block retTyVars q.1 q.2))))
    rw [show (fun (q : Identifier T.IDMeta × LMonoTy) => q.1.name)
          = (fun y : Identifier T.IDMeta => y.name) ∘ Prod.fst from rfl,
      ← List.map_map, List.map_fst_zip (Nat.le_of_eq hlensame)]
    exact genArgNames_names_nodup _
  · refine List.nodup_append.mpr ⟨hretnodup, hownnodup, ?_⟩
    intro a ha b hb hab
    exact hdisj a ha (hab ▸ hb)
  · intro ty hty
    rw [ListMap.values_eq_map_snd,
      List.map_snd_zip (Nat.le_of_eq hlensame.symm)] at hty
    exact fun v hv => hinput ty hty v hv
  · intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    rw [hv]
    exact List.mem_append_left _ houtmem
  · intro _ hb; exact absurd hb (by simp)
  · intro _ hp; exact absurd hp (by simp)
  · intro hc; exact absurd hc (by simp)
  · intro ta hta
    rcases List.mem_append.mp hta with hret | hown
    · exact Bool.ne_true_of_eq_false (hretgen ta hret)
    · exact Bool.ne_true_of_eq_false (howngen ta hown)
  · intro fn md opTy args res hfn heval
    simp only [Option.some.injEq] at hfn
    subst hfn
    rw [elimConcreteEval_length block m md opTy args res heval, List.length_zip,
      ← hlensame, genArgNames_length, hcount]
    simp
  · simp
  · intro ceval hceval md1 md2 opTy args1 args2 res1 hmap heval
    simp only [Option.some.injEq] at hceval
    subst hceval
    exact elimConcreteEval_eraseMetadata block m md1 md2 opTy args1 args2 res1 hmap
      heval
  · intro ceval hceval md opTy args res heval z hz
    simp only [Option.some.injEq] at hceval
    subst hceval
    exact elimConcreteEval_getVars block m md opTy args res heval z hz

/-- Every eliminator a mutual block generates is well formed when each
    datatype's type parameters are distinct and none of them starts with
    `genTyPrefix`, all datatypes of the block have the same set of type
    parameters, and every constructor field type uses only its datatype's
    parameters. -/
private theorem elimFuncs_wf {T : LExprParams} [Inhabited T.IDMeta]
    [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (m : T.Metadata)
    (hnodup : ∀ d ∈ block, d.typeArgs.Nodup)
    (hagree : ∀ d ∈ block, ∀ d' ∈ block, ∀ v, v ∈ d.typeArgs ↔ v ∈ d'.typeArgs)
    (hres : ∀ d ∈ block, ∀ v ∈ d.typeArgs,
      genTyPrefix.toList.isPrefixOf v.toList = false)
    (hscoped : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs) :
    ∀ f ∈ elimFuncs (T := T) block m, LFuncWF f := by
  intro f hf
  simp only [elimFuncs] at hf
  elim_err hf with hne
  have hblocklen : 0 < block.length := by
    rcases block with _ | ⟨_, _⟩
    · exact absurd rfl hne
    · simp
  obtain ⟨p, hp, hpf⟩ := List.mem_map.mp hf
  obtain ⟨d, outputTyVar⟩ := p
  have hd : d ∈ block := (List.of_mem_zip hp).1
  have houtmem : outputTyVar ∈ freshTypeArgs block.length block[0].typeArgs :=
    (List.of_mem_zip hp).2
  subst hpf
  refine elimFunc_wf block m d _ outputTyVar _ (hnodup d hd)
    (freshTypeArgs_nodup _ _) ?_ (freshTypeArgs_length _ _) houtmem ?_
    (hres d hd) (length_blockConstrs block) ?_
  · intro v hv hvd
    exact freshTypeArgs_not_mem _ _ v hv
      ((hagree d hd block[0] (List.getElem_mem hblocklen) v).mp hvd)
  · intro v hv
    obtain ⟨i, hi⟩ := freshTypeArgs_mem_elimTyPrefix _ _ v hv
    rw [hi]
    exact genTyPrefix_not_prefix_elimTyName i
  · intro q hq
    obtain ⟨hlt, hcmem⟩ := mem_blockConstrs block q.1 q.2 hq
    refine ⟨hlt, ?_⟩
    intro arg harg w hw
    exact (hagree block[q.1] (List.getElem_mem hlt) d hd w).mp
      (hscoped block[q.1] (List.getElem_mem hlt) q.2 hcmem arg harg w hw)

/-! ### All generated functions -/

/-- Every function generated for a block is well formed when the block passes
    validation and the check that its constructor fields use only the
    datatype's type parameters. -/
theorem genBlockFactory_wf {T : LExprParams} [DecidableEq T.IDMeta]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] [ToFormat T.IDMeta]
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    (hval : validateMutualBlock block = .ok ())
    (hvars : checkConstructorArgVarsScoped block = .ok ())
    (hgen : genBlockFactory block = .ok fac) :
    ∀ f ∈ fac.toArray, LFuncWF f := by
  obtain ⟨-, -, hagree, hnodup, hreserved⟩ :=
    validateMutualBlock_sound block hval
  have hres : ∀ d ∈ block, ∀ v ∈ d.typeArgs,
      genTyPrefix.toList.isPrefixOf v.toList = false :=
    fun d hd v hv =>
      Bool.eq_false_iff.mpr
        (not_genTyPrefix_of_isAllowedName (hreserved d hd v hv))
  have hscoped := checkConstructorArgVarsScoped_sound block hvars
  have hargnames := genBlockFactory_constr_args_nodup block fac hgen
  intro f hf
  rcases mem_genBlockFactory hgen hf with
    helim | ⟨d, hd, c, hc, rfl⟩ | ⟨d, hd, c, hc, rfl⟩ | ⟨d, hd, c, hc, hcf⟩ |
      ⟨d, hd, c, hc, hcf⟩
  · exact elimFuncs_wf block default hnodup hagree hres hscoped f helim
  · exact constrFunc_wf d c (hargnames d hd c hc) (hnodup d hd)
      (hscoped d hd c hc) (hres d hd)
  · exact testerFunc_wf block d c default (hnodup d hd) (hres d hd)
  · exact destructorFuncs_wf d c true (hnodup d hd) (hscoped d hd c hc)
      (hres d hd) f hcf
  · exact destructorFuncs_wf d c false (hnodup d hd) (hscoped d hd c hc)
      (hres d hd) f hcf

/-- If a context accepts a mutual block, `genBlockFactory` succeeds on that
    block and every function it generates is well formed. -/
theorem LContext.addMutualBlock_genBlockFactory_wf {T : LExprParams}
    [DecidableEq T.IDMeta] [Inhabited T.IDMeta] [Inhabited T.Metadata]
    [ToFormat T.IDMeta] {C C' : LContext T} {block : MutualDatatype T.IDMeta}
    (h : C.addMutualBlock block = .ok C') :
    ∃ fac, genBlockFactory block = .ok fac ∧ ∀ f ∈ fac.toArray, LFuncWF f := by
  obtain ⟨-, ds, fac, -, -, hds, hgen, -, -, -⟩ :=
    LContext.addMutualBlock_ok_eq C C' block h
  obtain ⟨hval, -, hvars, -⟩ :=
    TypeFactory.addMutualBlock_ok_inv C.datatypes ds block C.knownTypes hds
  exact ⟨fac, hgen, genBlockFactory_wf block fac hval hvars hgen⟩

/-! ### Signatures of generated functions -/

/-- Let `P` be a property of types that holds for every type variable, for
    `bool`, for each datatype of the block applied to its own type parameters
    and for each constructor argument type, and that holds for an arrow exactly
    when it holds for both sides. Then every input and output type of every
    function the block generates has `P`. -/
theorem genBlockFactory_sigs_of {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    (P : LMonoTy → Prop) (h_ftvar : ∀ v, P (.ftvar v))
    (h_arrow : ∀ a b, P a → P b → P (LMonoTy.arrow a b))
    (h_split : ∀ a b, P (LMonoTy.arrow a b) → P a ∧ P b)
    (h_bool : P LMonoTy.bool)
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    (hdata : ∀ d ∈ block, P (dataDefault d))
    (hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, P arg.2)
    (hgen : genBlockFactory block = .ok fac) :
    ∀ f ∈ fac.toArray, ∀ ty ∈ f.output :: f.inputs.values, P ty := by
  intro f hf
  have hdestr : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ b : Bool,
      ∀ g ∈ (bif b then destructorFuncs (T := T) d c
        else unsafeDestructorFuncs d c),
      ∀ ty ∈ g.output :: g.inputs.values, P ty := by
    intro d hd c hc b g hg
    cases b
    all_goals
      simp only [Bool.cond_true, Bool.cond_false, destructorFuncs,
        unsafeDestructorFuncs, List.mem_mapIdx] at hg
      obtain ⟨k, hk, hkEq⟩ := hg
      rw [← hkEq]
      refine List.forall_mem_cons.mpr
        ⟨hargs d hd c hc c.args[k] (List.getElem_mem hk), ?_⟩
      intro ty hty
      simp only [mkDestructorFunc] at hty
      rw [ListMap.values_eq_map_snd [(_, _)], List.map_cons, List.map_nil,
        List.mem_singleton] at hty
      rw [hty]
      exact hdata d hd
  rcases mem_genBlockFactory hgen hf with
    helim | ⟨d, hd, c, hc, rfl⟩ | ⟨d, hd, c, hc, rfl⟩ | ⟨d, hd, c, hc, hcf⟩ |
      ⟨d, hd, c, hc, hcf⟩
  · simp only [elimFuncs] at helim
    split at helim
    · exact absurd helim (by simp)
    obtain ⟨p, hp, hpf⟩ := List.mem_map.mp helim
    obtain ⟨d, outputTyVar⟩ := p
    have hd : d ∈ block := (List.of_mem_zip hp).1
    rw [← hpf]
    refine List.forall_mem_cons.mpr ⟨h_ftvar _, ?_⟩
    intro ty hty
    rw [ListMap.values_eq_map_snd] at hty
    obtain ⟨q, hq, hqty⟩ := List.mem_map.mp hty
    have hqsnd := (List.of_mem_zip hq).2
    rw [← hqty]
    rcases List.mem_cons.mp hqsnd with hdef | hcase
    · rw [hdef]
      exact hdata d hd
    · obtain ⟨r, hr, hrty⟩ := List.mem_map.mp hcase
      obtain ⟨hlt, hcmem⟩ := mem_blockConstrs block r.1 r.2 hr
      rw [← hrty]
      exact prop_elimTy P h_ftvar h_arrow h_split block _ r.1 r.2
        (hargs block[r.1] (List.getElem_mem hlt) r.2 hcmem)
  · refine List.forall_mem_cons.mpr ⟨hdata d hd, ?_⟩
    intro ty hty
    simp only [constrFunc] at hty
    rw [ListMap.values_eq_map_snd c.args] at hty
    obtain ⟨arg, harg, hargEq⟩ := List.mem_map.mp hty
    rw [← hargEq]
    exact hargs d hd c hc arg harg
  · refine List.forall_mem_cons.mpr ⟨h_bool, ?_⟩
    intro ty hty
    simp only [testerFunc] at hty
    rw [ListMap.values_eq_map_snd [(_, _)], List.map_cons, List.map_nil,
      List.mem_singleton] at hty
    rw [hty]
    exact hdata d hd
  · exact hdestr d hd c hc true f hcf
  · exact hdestr d hd c hc false f hcf

/-- Every input and output type of every function a mutual block generates
    names only type constructors without a reserved prefix, when the block's
    datatype names and constructor argument types have none. -/
theorem genBlockFactory_sigsAllowed {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    (hnames : ∀ d ∈ block, isAllowedName d.name = true)
    (hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      mtyAllTyConsNames isAllowedName arg.2 = true)
    (hgen : genBlockFactory block = .ok fac) :
    ∀ f ∈ fac.toArray, ∀ ty ∈ f.output :: f.inputs.values,
      mtyAllTyConsNames isAllowedName ty = true := by
  exact genBlockFactory_sigs_of
    (fun ty => mtyAllTyConsNames isAllowedName ty = true)
    (mtyAllTyConsNames_ftvar isAllowedName)
    (fun _ _ ha hb => mtyAllTyConsNames_arrow isAllowedName_arrow ha hb)
    (fun _ _ h => mtyAllTyConsNames_arrow_inv h)
    ((mtyAllTyConsNames_bool isAllowedName).trans isAllowedName_bool) block fac
    (fun d hd => mtyAllTyConsNames_dataDefault isAllowedName d (hnames d hd))
    hargs hgen

end

end Lambda
