import Lean
import Strata.Languages.Core.SMTEncoder

/-!
# Denotation of SMT terms for the Strata DSL

This module interprets the shallowly embedded SMT term language into Lean
types. The interpretation is partial because not every SMT feature is
currently supported. The core entry point is `denoteTerm`, which builds a
`TermDenoteResult` describing both the type of a term and a semantic interpreter
for it. The surrounding infrastructure tracks the well-formedness of
term and uninterpreted-function contexts so that evaluation is safe.
-/

open Strata.SMT

theorem List.getElem_of_findIdx?_eq_some {xs : List α} {mkTypeFunType : α → Bool} {i : Nat}
    (h : xs.findIdx? mkTypeFunType = some i) : mkTypeFunType (xs[i]'((List.findIdx?_eq_some_iff_findIdx_eq.mp h).left)) := by
  have ⟨h1, h2⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact h2.1

def mkTypeFunType (n : Nat) : Type 1 := n.repeat (Type → ·) Type

def applyTypeArg {n : Nat} (tf : mkTypeFunType (n + 1)) (α : Type) : mkTypeFunType n :=
  tf α

def applyTypeArgs {n : Nat} (tf : mkTypeFunType n) (αs : List Type) (h : αs.length = n) : Type :=
  match n, αs with
  | 0, []          => tf
  | _ + 1, α :: αs => applyTypeArgs (applyTypeArg tf α) αs (propext Nat.add_one_inj ▸ List.length_cons ▸ h)

def mkNonemptyPred {n : Nat} (us : mkTypeFunType n) : Prop :=
  match n with
  | 0     => Nonempty us
  | _ + 1 => ∀ (α : Type), mkNonemptyPred (applyTypeArg us α)

def applyNonemptyPred {n : Nat} {fα : mkTypeFunType n} (hfα : mkNonemptyPred fα) (αs : List Type) (h : αs.length = n) :
    Nonempty (applyTypeArgs fα αs h) :=
  match n, αs with
  | 0, []          => hfα
  | _ + 1, α :: αs => applyNonemptyPred (hfα α) αs (propext Nat.add_one_inj ▸ List.length_cons ▸ h)

structure USDenote where
  us   : Core.SMT.Sort
  usΓ  : mkTypeFunType us.arity
  nonempty : mkNonemptyPred usΓ

abbrev USContext := List Core.SMT.Sort
abbrev USEnvironment := List USDenote

structure USEnvironment.WF (uss : USContext) (Γ : USEnvironment) where
  h : uss.length = Γ.length
  ha : ∀ i, (hi : i < uss.length) → uss[i] = Γ[i].us

/-- Context for type synonyms. Maps a sort name to its type,
    which is assumed to not contain other type synonyms.
    Denotation fails if this is violated -/
abbrev ISContext := Map String TermType

structure SortContext where
  uss : USContext := []
  iss : ISContext := {}

abbrev SortEnvironment := USEnvironment

abbrev SortEnvironment.WF (sctx : SortContext) (Γ : SortEnvironment) :=
  USEnvironment.WF sctx.uss Γ

structure SortDenoteInput (sctx : SortContext) where
  sΓ : SortEnvironment
  hsΓ : sΓ.WF sctx

abbrev SortDenoteResult (sctx : SortContext) :=
  SortDenoteInput sctx → Type

mutual

def substituteIS (iss : ISContext) (ty : TermType) : TermType :=
  match ty with
  | .prim _ => ty
  | .option ty => .option (substituteIS iss ty)
  | .constr id args =>
    match iss.find? id with
    | some ty' => ty'
    | none     => .constr id (substituteISs iss args)

def substituteISs (iss : ISContext) (tys : List TermType) : List TermType :=
  match tys with
  | []        => []
  | ty :: tys => substituteIS iss ty :: substituteISs iss tys

end

def substituteTermVarIS (isctx : ISContext) (v : TermVar) : TermVar :=
  { v with ty := substituteIS isctx v.ty }

def substituteUFIS (isctx : ISContext) (uf : UF) : UF :=
  { uf with args := uf.args.map (substituteTermVarIS isctx), out := substituteIS isctx uf.out }

mutual

def substituteTermIS (isctx : ISContext) (t : Term) : Term :=
  match t with
  | .prim v =>
    .prim v
  | .var v =>
    .var (substituteTermVarIS isctx v)
  | .none ty =>
    .none (substituteIS isctx ty)
  | .some t =>
    .some (substituteTermIS isctx t)
  | .app (.uf f) as ty =>
    .app (.uf (substituteUFIS isctx f)) (substituteTermISs isctx as) (substituteIS isctx ty)
  | .app op as ty =>
    .app op (substituteTermISs isctx as) (substituteIS isctx ty)
  | .quant q vs t b =>
    .quant q (vs.map (substituteTermVarIS isctx)) (substituteTermIS isctx t) (substituteTermIS isctx b)

def substituteTermISs (isctx : ISContext) (ts : List Term) : List Term :=
  match ts with
  | [] => []
  | t :: ts => substituteTermIS isctx t :: substituteTermISs isctx ts

end

def substituteIFIS (isctx : ISContext) (iF : Core.SMT.IF) : Core.SMT.IF :=
  { iF with uf := substituteUFIS isctx iF.uf, body := substituteTermIS isctx iF.body }

mutual

/--
Interpret an SMT `TermType` as a Lean `Type`, when supported.

Returns `none` when we lack an interpretation (e.g. for reals).

Note: similar to `denoteSort`, but does not attempt to look up type synonyms.
-/
def denoteSortAux (sctx : SortContext) (ty : TermType) : Option (SortDenoteResult sctx) := do
  match ty with
  | .prim .bool => return fun _ => Prop
  | .prim .int => return fun _ => Int
  | .prim (.bitvec n) => return fun _ => BitVec n
  -- We don't have access to `Real` in `Strata`, so we leave it as `none` for now.
  | .prim .real => none -- fin _ => Real
  | .prim .string => return fun _ => String
  | .prim .regex => none
  | .prim .trigger => none
  | .option ty =>
    let ty ← denoteSortAux sctx ty
    return fun sΓ => Option (ty sΓ)
  | .constr id args =>
    match hi : sctx.uss.findIdx? (·.name == id) with
    | some i =>
      have hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left
      let tys ← denoteSortsAux sctx args
      if h : tys.length = sctx.uss[i].arity then
        return fun ⟨sΓ, hΓ⟩ =>
          have _ : i < sΓ.length := hΓ.h ▸ hi
          applyTypeArgs sΓ[i].usΓ (tys.map (· ⟨sΓ, hΓ⟩)) (List.length_map _ ▸ hΓ.ha i hi ▸ h)
      else
        none
    | none => none

def denoteSortsAux (sctx : SortContext) (tys : List TermType) : Option (List (SortDenoteResult sctx)) := do
  match tys with
  | [] => return []
  | a :: as =>
    let a ← denoteSortAux sctx a
    let as ← denoteSortsAux sctx as
    return a :: as

end

mutual

/--
Interpret an SMT `TermType` as a Lean `Type`, when supported.

Returns `none` when we lack an interpretation (e.g. for reals).
-/
def denoteSort (sctx : SortContext) (ty : TermType) : Option (SortDenoteResult sctx) := do
  match ty with
  | .prim .bool => return fun _ => Prop
  | .prim .int => return fun _ => Int
  | .prim (.bitvec n) => return fun _ => BitVec n
  -- We don't have access to `Real` in `Strata`, so we leave it as `none` for now.
  | .prim .real => none -- fin _ => Real
  | .prim .string => return fun _ => String
  | .prim .regex => none
  | .prim .trigger => none
  | .option ty =>
    let ty ← denoteSort sctx ty
    return fun sΓ => Option (ty sΓ)
  | .constr id args =>
    match hi : sctx.uss.findIdx? (·.name == id) with
    | some i =>
      have hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left
      let tys ← denoteSorts sctx args
      if h : tys.length = sctx.uss[i].arity then
        return fun ⟨sΓ, hΓ⟩ =>
          have _ : i < sΓ.length := hΓ.h ▸ hi
          applyTypeArgs sΓ[i].usΓ (tys.map (· ⟨sΓ, hΓ⟩)) (List.length_map _ ▸ hΓ.ha i hi ▸ h)
      else
        none
    | none => match hi : sctx.iss.find? id with
      | some ty => denoteSortAux sctx ty
      | none => none

def denoteSorts (sctx : SortContext) (tys : List TermType) : Option (List (SortDenoteResult sctx)) := do
  match tys with
  | [] => return []
  | a :: as =>
    let a ← denoteSort sctx a
    let as ← denoteSorts sctx as
    return a :: as

end

/--
Interpret a function type described by SMT term variables and a return type.

The result is an arrow type `a₁ → … → out` when every argument and the
result type can be interpreted.
-/
@[simp]
def denoteFunSort (sctx : SortContext) (as : List TermVar) (out : TermType) : Option (SortDenoteResult sctx) :=
  match as with
  | []      => denoteSort sctx out
  | a :: as => do
    let a ← denoteSort sctx a.ty
    let as ← denoteFunSort sctx as out
    return fun sΓ => a sΓ → as sΓ

theorem denoteSortOption_isSome (h : (denoteSort sctx (.option ty)).isSome) :
    (denoteSort sctx ty).isSome := by
  exact Option.isSome_of_isSome_bind h

theorem isSome_denoteSortOption (h : (denoteSort sctx ty).isSome) :
    (denoteSort sctx (.option ty)).isSome := by
  simp [denoteSort, Option.isSome_bind, h]

theorem denoteSortOption_Some :
  (denoteSort sctx (.option ty)).get h sΓ = Option ((denoteSort sctx ty).get (denoteSortOption_isSome h) sΓ) := by
  simp [denoteSort]

theorem denoteFunSortCons_isSome (h : (denoteFunSort sctx (a :: as) out).isSome) :
    (denoteSort sctx a.ty).isSome ∧ (denoteFunSort sctx as out).isSome := by
  simp only [denoteFunSort, Option.pure_def, Option.bind_eq_bind,
              Option.isSome_bind, Option.isSome_some, Option.any_true] at h
  have ⟨h1 , h2⟩ := (Option.any_eq_true_iff_get _ _).mp h
  exact ⟨h1, h2⟩

theorem arrow_of_denoteFunSortCons_isSome (h : (denoteFunSort sctx (a :: as) out).isSome) :
    have has := denoteFunSortCons_isSome h
    (denoteFunSort sctx (a :: as) out).get h sΓ =
    ((denoteSort sctx a.ty).get has.left sΓ → (denoteFunSort sctx as out).get has.right sΓ) := by
  simp [*, denoteFunSort] at *

theorem denoteSortOut_isSome_of_denoteFunSort_isSome (h : (denoteFunSort sctx as out).isSome) :
    (denoteSort sctx out).isSome := by
  induction as
  case nil => exact h
  case cons head tail ih =>
    simp only [denoteFunSort, Option.pure_def, Option.bind_eq_bind,
               Option.isSome_bind, Option.isSome_some, Option.any_true] at h
    have ⟨h1 , h2⟩ := (Option.any_eq_true_iff_get _ _).mp h
    exact ih h2

/--
Runtime value paired with a term-variable declaration and a proof that the
type can be interpreted.
-/
structure TermVarDenote (sΓ : SortDenoteInput sctx) where
  var  : TermVar
  h    : (denoteSort sctx var.ty).isSome
  varΓ : (denoteSort sctx var.ty).get h sΓ

abbrev TermVarContext := List TermVar
abbrev TermVarEnvironment (sΓ : SortDenoteInput sctx) := List (TermVarDenote sΓ)

/--
Well-formedness predicate ensuring that an interpreted term-variable
environment matches its syntactic context.
-/
structure TermVarEnvironment.WF (vs : TermVarContext) (tΓ : TermVarEnvironment sΓ) where
  h : vs.length = tΓ.length
  ha : ∀ i, (hi : i < vs.length) → vs[i] = tΓ[i].var

/--
Runtime function paired with the corresponding uninterpreted-function
declaration and interpretation witness.
-/
structure UFDenote (sΓ : SortDenoteInput sctx) where
  uf  : UF
  h   : (denoteFunSort sctx uf.args uf.out).isSome
  ufΓ : (denoteFunSort sctx uf.args uf.out).get h sΓ

abbrev UFContext := List UF
abbrev UFEnvironment (sΓ : SortDenoteInput sctx) := List (UFDenote sΓ)

/--
Well-formedness predicate ensuring that an interpreted uninterpreted-function
environment aligns with the syntactic declarations.
-/
structure UFEnvironment.WF (ufs : UFContext) (Γ : UFEnvironment sΓ) where
  h : ufs.length = Γ.length
  ha : ∀ i, (hi : i < ufs.length) → ufs[i] = Γ[i].uf

/--
Syntactic context tracking the declared term variables and uninterpreted
functions that may appear in a term.
-/
structure TermContext where
  vs  : TermVarContext := []
  ufs : UFContext := []

/--
Semantic environment providing Lean values for the elements stored in a
`Context`.
-/
structure TermEnvironment (sΓ : SortDenoteInput sctx) where
  vs  : TermVarEnvironment sΓ
  ufs : UFEnvironment sΓ

/--
Well-formedness predicate linking a semantic `Environment` with the
corresponding syntactic `Context`.
-/
structure TermEnvironment.WF (tctx : TermContext) (Γ : TermEnvironment sΓ) : Prop where
  hv : Γ.vs.WF tctx.vs
  huf : Γ.ufs.WF tctx.ufs

structure Context where
  sctx : SortContext := {}
  tctx : TermContext := {}

/--
Bundle pairing an environment with a proof that it realises a particular
context. This is the argument given to semantic interpreters.
-/
structure TermDenoteInput (ctx : Context) where
  sΓ : SortEnvironment
  hsΓ : sΓ.WF ctx.sctx
  tΓ : TermEnvironment ⟨sΓ, hsΓ⟩
  htΓ : tΓ.WF ctx.tctx

/--
Result of attempting to interpret a term: carries its type, a proof that the
type is supported, and a semantic interpreter.
-/
structure TermDenoteResult (ctx : Context) where
  ty : TermType
  h : (denoteSort ctx.sctx ty).isSome
  res : (tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩

-- Note: `noncomputable` due to a compiler error
/--
Check that the denotations `as` match the types of the variables `vs` when the
two lists have the same length.
-/
@[simp]
noncomputable def argTypesAlignAux (as : List (TermDenoteResult ctx)) (vs : List TermVar) (hl : as.length = vs.length) : Bool :=
  match as, vs with
  | [], [] => true
  | a :: as, v :: vs =>
    a.ty == v.ty && argTypesAlignAux as vs (Nat.succ.inj hl)
  | _, _ => false

-- Note: `noncomputable` because `argTypesAlignAux` is `noncomputable` due to a compiler error
/--
Check that the argument denotations align with the declared term-variable types.
-/
@[simp]
noncomputable def argTypesAlign (as : List (TermDenoteResult ctx)) (vs : List TermVar) : Bool :=
  if h : as.length = vs.length then
    argTypesAlignAux as vs h
  else
    false

theorem argTypesAlignAux_true (h : argTypesAlignAux as vs hl) :
  ∀ i, (h : i < as.length) → as[i].ty = (vs[i]'(hl ▸ h)).ty := fun i hi =>
  match as, vs with
  | [], _ => nomatch h
  | a :: as, v :: vs =>
    match i with
    | 0 => eq_of_beq (Bool.and_eq_true_iff.mp h).left
    | i + 1 =>
      (List.getElem_cons_succ a as i hi).symm ▸ (List.getElem_cons_succ v vs i (hl ▸ hi)).symm ▸
      argTypesAlignAux_true (Bool.and_eq_true_iff.mp h).right i (Nat.lt_of_succ_lt_succ hi)

theorem argTypesAlign_length_eq (h : argTypesAlign as vs) : as.length = vs.length := by
  unfold argTypesAlign at h
  by_cases hl : as.length = vs.length
  case pos => exact hl
  case neg => rewrite [dif_neg hl] at h; contradiction

theorem argTypesAlign_arg_types (h : argTypesAlign as vs) :
  ∀ i, (hi : i < as.length) → as[i].ty = (vs[i]'(argTypesAlign_length_eq h ▸ hi)).ty := by
  unfold argTypesAlign at h
  by_cases hl : as.length = vs.length
  case pos => exact argTypesAlignAux_true (dif_pos hl ▸ h)
  case neg =>
    rewrite [dif_neg hl] at h; contradiction

-- Note: `noncomputable` because of a compiler error
/--
Apply an interpreted uninterpreted function to a list of argument denotations.
-/
@[simp]
noncomputable def applyUF (tdi : TermDenoteInput ctx) (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
  (as : List (TermDenoteResult ctx)) (hl : args.length = as.length) (has : ∀ i, (hi : i < as.length) → as[i].ty = (args[i]'(hl ▸ hi)).ty) :
    (denoteSort ctx.sctx out).get (denoteSortOut_isSome_of_denoteFunSort_isSome h) ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  match args, as with
  | [], []            => uf
  | arg :: _, a :: as =>
    let uf := arrow_of_denoteFunSortCons_isSome h ▸ uf
    have ha : denoteSort ctx.sctx arg.ty = denoteSort ctx.sctx a.ty := has 0 (Nat.zero_lt_succ _) ▸ rfl
    let uf := uf (Option.get_congr ha ▸ a.res tdi)
    applyUF tdi uf as (Nat.succ.inj hl) (fun i hi => (has (i + 1) (Nat.succ_lt_succ hi)))

@[simp]
def bindForallVar (ctx : Context) (hTy : (denoteSort ctx.sctx ty).isSome) :
    let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
    let v' := { id := n, ty := ty }
    let vs' := v' :: ctx.tctx.vs
    let tctx' := { ufs := ctx.tctx.ufs, vs := vs' }
    (TermDenoteInput ⟨ctx.sctx, tctx'⟩ → Prop) →
    TermDenoteInput ⟨ctx.sctx, tctx⟩ → Prop :=
  let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
  let v' := { id := n, ty := ty }
  let vs' := v' :: ctx.tctx.vs
  let tctx' : TermContext := { ufs := ctx.tctx.ufs, vs := vs' }
  fun ft' (tdi : TermDenoteInput ⟨ctx.sctx, tctx⟩) =>
    ∀ (x : (denoteSort ctx.sctx v'.ty).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩),
      let v' := { var := v', h := hTy, varΓ := x }
      let vΓ' : TermVarEnvironment ⟨tdi.sΓ, tdi.hsΓ⟩ := v' :: tdi.tΓ.vs
      have hv' : vΓ'.WF vs' :=
        have h' := show _ + _ = _ + _ from tdi.htΓ.hv.h ▸ rfl
        have ha' := fun i hivs => match i with
          | 0 => rfl
          | i + 1 =>
            have hivs' := Nat.lt_of_succ_lt_succ hivs
            have hivΓ := Nat.succ_lt_succ (tdi.htΓ.hv.h ▸ hivs')
            (List.getElem_cons_succ _ ctx.tctx.vs i hivs).symm ▸ (List.getElem_cons_succ _ tdi.tΓ.vs i hivΓ).symm ▸ tdi.htΓ.hv.ha i hivs'
        { h := h', ha := ha' }
      let tdi' : TermDenoteInput ⟨ctx.sctx, tctx'⟩ :=
        { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ, tΓ := { ufs := tdi.tΓ.ufs, vs := vΓ' }, htΓ := { hv := hv', huf := tdi.htΓ.huf } }
      ft' tdi'

def buildForall (ctx : Context) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome)
    (bodyFt : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (tdi : TermDenoteInput ctx)
    : Prop :=
    match vs with
    | [] => bodyFt tdi
    | { id := n, ty := ty } :: vs =>
      have hTys' := (denoteFunSortCons_isSome hTys).right
      letI ctx' : Context := { sctx := ctx.sctx, tctx := { vs := { id := n, ty := ty } :: ctx.tctx.vs, ufs := ctx.tctx.ufs } }
      have hvs : ({ id := n, ty := ty } :: vs).reverse ++ ctx.tctx.vs = vs.reverse ++ ctx'.tctx.vs :=
        List.reverse_cons ▸ List.append_assoc _ _ _ ▸ rfl
      let ft' := buildForall ctx' vs hTys' (hvs ▸ bodyFt)
      bindForallVar ctx (denoteFunSortCons_isSome hTys).left ft' tdi

@[simp]
def bindExistsVar (ctx : Context) (hTy : (denoteSort ctx.sctx ty).isSome) :
    let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
    let v' := { id := n, ty := ty }
    let vs' := v' :: ctx.tctx.vs
    let tctx' := { ufs := ctx.tctx.ufs, vs := vs' }
    (TermDenoteInput ⟨ctx.sctx, tctx'⟩ → Prop) →
    TermDenoteInput ⟨ctx.sctx, tctx⟩ → Prop :=
  let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
  let v' := { id := n, ty := ty }
  let vs' := v' :: ctx.tctx.vs
  let tctx' : TermContext := { ufs := ctx.tctx.ufs, vs := vs' }
  fun ft' (tdi : TermDenoteInput ⟨ctx.sctx, tctx⟩) =>
    ∃ (x : (denoteSort ctx.sctx v'.ty).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩),
      let v' := { var := v', h := hTy, varΓ := x }
      let vΓ' : TermVarEnvironment ⟨tdi.sΓ, tdi.hsΓ⟩ := v' :: tdi.tΓ.vs
      have hv' : vΓ'.WF vs' :=
        have h' := show _ + _ = _ + _ from tdi.htΓ.hv.h ▸ rfl
        have ha' := fun i hivs => match i with
          | 0 => rfl
          | i + 1 =>
            have hivs' := Nat.lt_of_succ_lt_succ hivs
            have hivΓ := Nat.succ_lt_succ (tdi.htΓ.hv.h ▸ hivs')
            (List.getElem_cons_succ _ ctx.tctx.vs i hivs).symm ▸ (List.getElem_cons_succ _ tdi.tΓ.vs i hivΓ).symm ▸ tdi.htΓ.hv.ha i hivs'
        { h := h', ha := ha' }
      let tdi' : TermDenoteInput ⟨ctx.sctx, tctx'⟩ :=
        { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ, tΓ := { ufs := tdi.tΓ.ufs, vs := vΓ' }, htΓ := { hv := hv', huf := tdi.htΓ.huf } }
      ft' tdi'

def buildExists (ctx : Context) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome)
    (bodyFt : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (tdi : TermDenoteInput ctx)
    : Prop :=
    match vs with
    | [] => bodyFt tdi
    | { id := n, ty := ty } :: vs =>
      have hTys' := (denoteFunSortCons_isSome hTys).right
      letI ctx' : Context := { sctx := ctx.sctx, tctx := { vs := { id := n, ty := ty } :: ctx.tctx.vs, ufs := ctx.tctx.ufs } }
      have hvs : ({ id := n, ty := ty } :: vs).reverse ++ ctx.tctx.vs = vs.reverse ++ ctx'.tctx.vs :=
        List.reverse_cons ▸ List.append_assoc _ _ _ ▸ rfl
      let ft' := buildExists ctx' vs hTys' (hvs ▸ bodyFt)
      bindExistsVar ctx (denoteFunSortCons_isSome hTys).left ft' tdi

mutual

/-
Noncomputable because of `ite` case. Two conditions are needed to make this function computable:
- Disallow quantifiers in the condition of `ite`.
- Return a proof of decidability for each other `Prop`.
-/
/--
Attempt to interpret a single SMT term under `ctx`, returning its Lean type
and semantics when successful.
-/
noncomputable def denoteTerm (ctx : Context) (t : Term) : Option (TermDenoteResult ctx) := do
  match t with
  -- Variables and uninterpreted functions (UFs).
  | .var v@hv:{ id := n, ty := ty } =>
    if hTy : (denoteSort ctx.sctx v.ty).isSome then
      match h : ctx.tctx.vs.findIdx? (· == v) with
      | some i =>
        have hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left
        have hiv := of_decide_eq_true (List.getElem_of_findIdx?_eq_some h)
        let ft (tdi : TermDenoteInput ctx) :=
          have _ : i < tdi.tΓ.vs.length := tdi.htΓ.hv.h ▸ hi
          have hvΓ : denoteSort ctx.sctx v.ty = denoteSort ctx.sctx tdi.tΓ.vs[i].var.ty := hiv.symm ▸ tdi.htΓ.hv.ha i hi ▸ rfl
          Option.get_congr hvΓ ▸ tdi.tΓ.vs[i].varΓ
        return ⟨v.ty, hTy, ft⟩
      | none => none
    else
      none
  | .app (.uf uf) as _ =>
    if hTys : (denoteFunSort ctx.sctx uf.args uf.out).isSome then
      match h : ctx.tctx.ufs.findIdx? (· == uf) with
      | some i =>
        let as ← denoteTerms ctx as
        if hufas : argTypesAlign as uf.args then
          have hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left
          have hiuf := of_decide_eq_true (List.getElem_of_findIdx?_eq_some h)
          let ft (tdi : TermDenoteInput ctx) :=
            have _ : i < tdi.tΓ.ufs.length := tdi.htΓ.huf.h ▸ hi
            have hufΓ : denoteFunSort ctx.sctx uf.args uf.out = denoteFunSort ctx.sctx tdi.tΓ.ufs[i].uf.args tdi.tΓ.ufs[i].uf.out :=
              hiuf.symm ▸ tdi.htΓ.huf.ha i hi ▸ rfl
            @applyUF ctx uf.args uf.out hTys tdi
              (Option.get_congr hufΓ ▸ tdi.tΓ.ufs[i].ufΓ) as (argTypesAlign_length_eq hufas).symm (argTypesAlign_arg_types hufas)
          return ⟨uf.out, denoteSortOut_isSome_of_denoteFunSort_isSome hTys, ft⟩
        else
          none
      | none => none
    else
      none
  -- Quantifiers
  | .quant .all vs _ t =>
    if hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome then
      let tctx : Context := { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } }
      let ⟨.prim .bool, _, tFt⟩ ← denoteTerm tctx t | none
      return ⟨.prim .bool, rfl, buildForall ctx vs hTys tFt⟩
    else
      none
  | .quant .exist vs _ t =>
    if hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome then
      let tctx : Context := { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } }
      let ⟨.prim .bool, _, tFt⟩ ← denoteTerm tctx t | none
      return ⟨.prim .bool, rfl, buildExists ctx vs hTys tFt⟩
    else
      none
  -- SMT-Lib core theory
  | .prim (.bool b) =>
    if b = true then return ⟨.prim .bool, rfl, fun _ => True⟩ else return ⟨.prim .bool, rfl, fun _ => False⟩
  | .app .not [a] _ =>
    let ⟨.prim .bool, h, a⟩ ← denoteTerm ctx a | none
    return ⟨.prim .bool, h, fun Γ => ¬a Γ⟩
  | .app .and as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .bool) rfl (fun _ => And) as
  | .app .or as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .bool) rfl (fun _ => Or) as
  | .app .eq as _ =>
    let (a@⟨ty, h, _⟩ :: as) ← denoteTerms ctx as | none
    chainable ctx ty h (fun sdi => @Eq ((denoteSort ctx.sctx ty).get h sdi)) (a :: as)
  | .app .ite [c, a, b] rt =>
    let ⟨.prim .bool, _, c⟩ ← denoteTerm ctx c | none
    let ⟨ty₁, h₁, a⟩ ← denoteTerm ctx a
    let ⟨ty₂, _, b⟩ ← denoteTerm ctx b
    if h₁₂ : ty₁ = ty₂ then
      return ⟨ty₁, h₁, fun Γ => @ite _ (c Γ) (Classical.propDecidable (c Γ)) (a Γ) (h₁₂ ▸ b Γ)⟩
    else
      none
  | .app .implies as _ =>
    let as ← denoteTerms ctx as
    rightAssoc ctx (.prim .bool) rfl (fun _ p q => p → q) as
  -- SMT-Lib theory of integers
  | .app .le as _ =>
    let as ← denoteTerms ctx as
    chainable ctx (.prim .int) rfl (fun _ => @LE.le Int _) as
  | .app .lt as _ =>
    let as ← denoteTerms ctx as
    chainable ctx (.prim .int) rfl (fun _ => @LT.lt Int _) as
  | .app .ge as _ =>
    let as ← denoteTerms ctx as
    chainable ctx (.prim .int) rfl (fun _ => @GE.ge Int _) as
  | .app .gt as _ =>
    let as ← denoteTerms ctx as
    chainable ctx (.prim .int) rfl (fun _ => @GT.gt Int _) as
  | .prim (.int x) =>
    return ⟨.prim .int, rfl, fun _ => x⟩
  | .app .neg [x] _ =>
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim .int, rfl, fun Γ => @Neg.neg Int _ (x Γ)⟩
  | .app .sub as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .int) rfl (fun _ => @HSub.hSub Int Int Int _) as
  | .app .add as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .int) rfl (fun _ => @HAdd.hAdd Int Int Int _) as
  | .app .mul as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .int) rfl (fun _ => @HMul.hMul Int Int Int _) as
  | .app .div as _ =>
    -- Semantic mismatch with SMT-Lib: `x / 0` is defined as `0` in Lean, but as UF in SMT-Lib.
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .int) rfl (fun _ => @HDiv.hDiv Int Int Int _) as
  | .app .mod [x, y] _ =>
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    -- Semantic mismatch with SMT-Lib: `x % 0` is defined as `x` in Lean, but as UF in SMT-Lib.
    return ⟨.prim .int, rfl, fun Γ => @HMod.hMod Int Int Int _ (x Γ) (y Γ)⟩
  | .app .abs [x] _ =>
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim .int, rfl, fun Γ => if @LT.lt Int _ (x Γ) 0 then @Neg.neg Int _ (x Γ) else x Γ⟩
  -- SMT-Lib theory of bitvectors
  | .prim (.bitvec (n := n) bv) =>
    return ⟨.prim (.bitvec n), rfl, fun _ => bv⟩
  | .app .bvneg [x] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim (.bitvec n), rfl, fun Γ => @Neg.neg (BitVec n) _ (x Γ)⟩
  | .app .bvadd as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HAdd.hAdd (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvsub as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    -- Note: `bvsub` is not declared as `:left-assoc` in SMT-Lib, but we treat it as such here.
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HSub.hSub (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvmul as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HMul.hMul (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvnot [x] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim (.bitvec n), rfl, fun Γ => @Complement.complement (BitVec n) _ (x Γ)⟩
  | .app .bvand as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HAnd.hAnd (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvor as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HOr.hOr (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvxor as _ =>
    let (a@⟨.prim (.bitvec n), h, _⟩ :: as) ← denoteTerms ctx as | none
    -- Note: `bvxor` is not declared as `:left-assoc` in SMT-Lib, but we treat it as such here.
    leftAssoc ctx (.prim (.bitvec (n := n))) rfl (fun _ => @HXor.hXor (BitVec n) (BitVec n) (BitVec n) _) (a :: as)
  | .app .bvshl [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    -- Note: SMT-Lib does not allow `bvshl` to have different sizes for its two arguments, but we
    -- allow it here for convenience.
    return ⟨.prim (.bitvec n), rfl, fun Γ => @HShiftLeft.hShiftLeft (BitVec n) (BitVec m) (BitVec n) _ (x Γ) (y Γ)⟩
  | .app .bvlshr [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    -- Note: SMT-Lib does not allow `bvlshr` to have different sizes for its two arguments, but we
    -- allow it here for convenience.
    return ⟨.prim (.bitvec n), rfl, fun Γ => @HShiftRight.hShiftRight (BitVec n) (BitVec m) (BitVec n) _ (x Γ) (y Γ)⟩
  | .app .bvashr [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    -- Note: SMT-Lib does not allow `bvashr` to have different sizes for its two arguments, but we
    -- allow it here for convenience.
    return ⟨.prim (.bitvec n), rfl, fun Γ => BitVec.sshiftRight' (x Γ) (y Γ)⟩
  | .app .bvslt [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.slt (x Γ) (h ▸ y Γ) = true⟩
    else
      none
  | .app .bvsle [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.sle (x Γ) (h ▸ y Γ) = true⟩
    else
      none
  | .app .bvult [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => @LT.lt (BitVec n) _ (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvsge [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.sle (h ▸ y Γ) (x Γ) = true⟩
    else
      none
  | .app .bvsgt [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.slt (h ▸ y Γ) (x Γ) = true⟩
    else
      none
  | .app .bvule [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => @LE.le (BitVec n) _ (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvugt [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => @GT.gt (BitVec n) _ (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvuge [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => @GE.ge (BitVec n) _ (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvudiv [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim (.bitvec n), rfl, fun Γ => BitVec.smtUDiv (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvurem [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim (.bitvec n), rfl, fun Γ => @HMod.hMod (BitVec n) (BitVec n) (BitVec n) _ (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvsdiv [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim (.bitvec n), rfl, fun Γ => BitVec.smtSDiv (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvsrem [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim (.bitvec n), rfl, fun Γ => BitVec.srem (x Γ) (h ▸ y Γ)⟩
    else
      none
  | .app .bvnego [x] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim .bool, rfl, fun Γ => BitVec.negOverflow (x Γ) = true⟩
  | .app .bvsaddo [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.saddOverflow (x Γ) (h ▸ y Γ) = true⟩
    else
      none
  | .app .bvssubo [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.ssubOverflow (x Γ) (h ▸ y Γ) = true⟩
    else
      none
  | .app .bvsmulo [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    if h : n = m then
      return ⟨.prim .bool, rfl, fun Γ => BitVec.smulOverflow (x Γ) (h ▸ y Γ) = true⟩
    else
      none
  | .app .bvconcat [x, y] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim (.bitvec m), _, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim (.bitvec (n + m)), rfl, fun Γ => @HAppend.hAppend (BitVec n) (BitVec m) (BitVec (n + m)) _ (x Γ) (y Γ)⟩
  | .app (.zero_extend i) [x] _ =>
    let ⟨.prim (.bitvec n), _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim (.bitvec (n + i)), rfl, fun Γ => BitVec.zeroExtend (n + i) (x Γ)⟩
  -- SMT-Lib theory of strings
  | .prim (.string s) =>
    return ⟨.prim .string, rfl, fun _ => s⟩
  | .app .str_length [s] _ =>
    let ⟨.prim .string, _, s⟩ ← denoteTerm ctx s | none
    return ⟨.prim .int, rfl, fun Γ => Int.ofNat (s Γ).length⟩
  | .app .str_concat as _ =>
    let as ← denoteTerms ctx as
    leftAssoc ctx (.prim .string) rfl (fun _ => @HAppend.hAppend String String String _) as
  -- Option datatype
  | .app .option_get [a] _ =>
    let ⟨.option ty, h, a⟩ ← denoteTerm ctx a | none
    none
    -- Semantic mismatch with SMT-Lib: `Option.get a` requires a default value if `a` is `none` in Lean,
    -- but is a UF in SMT-Lib.
    -- return ⟨ty, denoteSortOption_isSome h, fun Γ => (denoteSortOption_Some ▸ a Γ).getD ??⟩
  | .none ty =>
    if h : (denoteSort ctx.sctx ty).isSome then
      return ⟨.option ty, isSome_denoteSortOption h, fun _ => denoteSortOption_Some ▸ none⟩
    else
      none
  | .some a =>
    let ⟨ty, h, a⟩ ← denoteTerm ctx a
    return ⟨.option ty, isSome_denoteSortOption h, fun Γ => denoteSortOption_Some ▸ some (a Γ)⟩
  | _ => none

-- Note: Using `List.mapM` breaks definitional equality for some reason, so we use a recursive function instead.
/--
Interpret every term in a list, short-circuiting if any sub-term fails.
-/
noncomputable def denoteTerms (ctx : Context) (ts : List Term) : Option (List (TermDenoteResult ctx)) := do
  match ts with
  | [] => return []
  | a :: as =>
    let a ← denoteTerm ctx a
    let as ← denoteTerms ctx as
    return a :: as

noncomputable def leftAssoc (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome)
    (op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi)
    (ts : List (TermDenoteResult ctx)) : Option (TermDenoteResult ctx) := do
  let t₁ :: t₂ :: ts := ts | none
  let ⟨ty₁, _, ft₁⟩ := t₁
  if h₁ : ty₁ = ty then
    let ⟨ty₂, _, ft₂⟩ := t₂
    if h₂ : ty₂ = ty then
      go (fun (tdi : TermDenoteInput ctx) => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h₁ ▸ ft₁ tdi) (h₂ ▸ ft₂ tdi)) ts
    else
      none
  else
    none
where
  go (ft : (tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩) (ts : List (TermDenoteResult ctx)) : Option (TermDenoteResult ctx) := do match ts with
    | []      => return ⟨ty, h, ft⟩
    | t :: ts =>
      let ⟨ty', _, ft'⟩ := t
      if h' : ty' = ty then
        go (fun (tdi : TermDenoteInput ctx) => op ⟨tdi.sΓ, tdi.hsΓ⟩ (ft tdi) (h' ▸ ft' tdi)) ts
      else
        none

noncomputable def rightAssoc (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome)
    (op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi)
    (ts : List (TermDenoteResult ctx)) : Option (TermDenoteResult ctx) := do
  let ft ← go ts
  return ⟨ty, h, ft⟩
where
  go (ts : List (TermDenoteResult ctx)) : Option ((tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩) := do match ts with
    | []    => none
    | [_]   => none
    | [t₂, t₁] =>
      let ⟨ty₁, _, ft₁⟩ := t₁
      if h₁ : ty₁ = ty then
        let ⟨ty₂, _, ft₂⟩ := t₂
        if h₂ : ty₂ = ty then
          return fun (tdi : TermDenoteInput ctx) => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h₂ ▸ ft₂ tdi) (h₁ ▸ ft₁ tdi)
        else
          none
      else
        none
    | t :: ts =>
      let ft ← go ts
      let ⟨ty', _, ft'⟩ := t
      if h' : ty' = ty then
        return fun (tdi : TermDenoteInput ctx) => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h' ▸ ft' tdi) (ft tdi)
      else
        none

noncomputable def chainable (ctx ty h)
    (op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi → Prop)
    (ts : List (TermDenoteResult ctx)) : Option (TermDenoteResult ctx) := do
  let t₁ :: t₂ :: ts := ts | none
  let ⟨ty₁, _, ft₁⟩ := t₁
  if h₁ : ty₁ = ty then
    let ⟨ty₂, _, ft₂⟩ := t₂
    if h₂ : ty₂ = ty then
      chainable.go ctx ty h op (fun (tdi : TermDenoteInput ctx) => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h₁ ▸ ft₁ tdi) (h₂ ▸ ft₂ tdi)) (h₂ ▸ ft₂) ts
    else
      none
  else
    none

noncomputable def chainable.go (ctx ty h)
    (op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi → Prop)
    (ft : TermDenoteInput ctx → Prop) (ft₁ : (tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (ts : List (TermDenoteResult ctx)) : Option (TermDenoteResult ctx) := do match ts with
  | []      => return ⟨.prim .bool, rfl, ft⟩
  | t₂ :: ts =>
    let ⟨ty₂, _, ft₂⟩ := t₂
    if h₂ : ty₂ = ty then
      chainable.go ctx ty h op (fun (tdi : TermDenoteInput ctx) => (ft tdi) ∧ op ⟨tdi.sΓ, tdi.hsΓ⟩ (ft₁ tdi) (h₂ ▸ ft₂ tdi)) (h₂ ▸ ft₂) ts
    else
      none

end

/--
Interpret a ground boolean term in the empty context.
-/
@[simp]
noncomputable def denoteBoolTermAux (t : Term) : Option Prop := do
  let some ⟨.prim .bool, _, fi⟩ := denoteTerm {} t | none
  return fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, ⟨[], []⟩, ⟨{ h := rfl, ha := fun _ hi => nomatch hi }, { h := rfl, ha := fun _ hi => nomatch hi }⟩⟩

/--
Interpret a ground integer term in the empty context.
-/
@[simp]
noncomputable def denoteIntTermAux (t : Term) : Option Int := do
  let some ⟨.prim .int, _, fi⟩ := denoteTerm {} t | none
  return fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, ⟨[], []⟩, ⟨{ h := rfl, ha := fun _ hi => nomatch hi }, { h := rfl, ha := fun _ hi => nomatch hi }⟩⟩

@[simp]
noncomputable def bindUS (uss iss) {us'} (ft' : SortDenoteInput ⟨(us' :: uss), iss⟩ → Prop) :
  Option (SortDenoteInput ⟨uss, iss⟩ → Prop) := do
  let sctx' : SortContext := ⟨(us' :: uss), iss⟩
  let ft (tdi : SortDenoteInput ⟨uss, iss⟩) :=
    set_option checkBinderAnnotations false in
    ∀ (α : mkTypeFunType us'.arity) [inst : mkNonemptyPred α],
      let us' := { us := us', usΓ := α, nonempty := inst }
      let usΓ' : USEnvironment := us' :: tdi.sΓ
      haveI hus' : usΓ'.WF sctx'.uss :=
        have h' := show _ + _ = _ + _ from tdi.hsΓ.h ▸ rfl
        have ha' := fun i hius => match i with
          | 0 => rfl
          | i + 1 =>
            have hius' := Nat.lt_of_succ_lt_succ hius
            have hiusΓ := Nat.succ_lt_succ (tdi.hsΓ.h ▸ hius')
            (List.getElem_cons_succ _ uss i hius).symm ▸ (List.getElem_cons_succ _ tdi.sΓ i hiusΓ).symm ▸ tdi.hsΓ.ha i hius'
        { h := h', ha := ha' }
      let tdi' : SortDenoteInput sctx' :=
        { sΓ := usΓ', hsΓ := hus' }
      ft' tdi'
  return ft

/--
Extend the context with an uninterpreted function and push its realisation into the denotation.
-/
@[simp]
noncomputable def bindUF {n} {args out} (ctx : Context) (ft' :
    let uf' := { id := n, args := args, out := out }
    let ufs' := uf' :: ctx.tctx.ufs
    let tctx' := { ufs := ufs', vs := ctx.tctx.vs }
    TermDenoteInput ⟨ctx.sctx, tctx'⟩ → Prop) :
  Option (TermDenoteInput ctx → Prop) := do
  if hTys : (denoteFunSort ctx.sctx args out).isSome then
    let uf' := { id := n, args := args, out := out }
    let ufs' := uf' :: ctx.tctx.ufs
    let tctx' : TermContext := { ufs := ufs', vs := ctx.tctx.vs }
    let ft (tdi : TermDenoteInput ctx) :=
      ∀ f : (denoteFunSort ctx.sctx args out).get hTys ⟨tdi.sΓ, tdi.hsΓ⟩,
        let uf' := { uf := uf', h := hTys, ufΓ := f }
        let ufΓ' : UFEnvironment ⟨tdi.sΓ, tdi.hsΓ⟩ := uf' :: tdi.tΓ.ufs
        haveI huf' : ufΓ'.WF ufs' :=
          have h' := show _ + _ = _ + _ from tdi.htΓ.huf.h ▸ rfl
          have ha' := fun i hiufs => match i with
            | 0 => rfl
            | i + 1 =>
              have hiufs' := Nat.lt_of_succ_lt_succ hiufs
              have hiufΓ := Nat.succ_lt_succ (tdi.htΓ.huf.h ▸ hiufs')
              (List.getElem_cons_succ _ ctx.tctx.ufs i hiufs).symm ▸ (List.getElem_cons_succ _ tdi.tΓ.ufs i hiufΓ).symm ▸ tdi.htΓ.huf.ha i hiufs'
          { h := h', ha := ha' }
        let tdi' : TermDenoteInput ⟨ctx.sctx, tctx'⟩ :=
          { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ, tΓ := { ufs := ufΓ', vs := tdi.tΓ.vs }, htΓ := { hv := tdi.htΓ.hv, huf := huf' } }
        ft' tdi'
    return ft
  else
    none

@[simp]
noncomputable def bindIFVar (ctx : Context) {hTys hTyTys} :
    let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
    let v' := { id := n, ty := ty }
    let vs' := v' :: ctx.tctx.vs
    let tctx' := { ufs := ctx.tctx.ufs, vs := vs' }
    ((tdi : TermDenoteInput ⟨ctx.sctx, tctx'⟩) → (denoteFunSort ctx.sctx vs out).get hTys ⟨tdi.sΓ, tdi.hsΓ⟩) →
    (tdi : TermDenoteInput ⟨ctx.sctx, tctx⟩) → (denoteFunSort ctx.sctx (v' :: vs) out).get hTyTys ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
  let v' := { id := n, ty := ty }
  let vs' := v' :: ctx.tctx.vs
  let tctx' : TermContext := { ufs := ctx.tctx.ufs, vs := vs' }
  have hTy := (denoteFunSortCons_isSome hTyTys).left
  fun ft' (tdi : TermDenoteInput ⟨ctx.sctx, tctx⟩) =>
    arrow_of_denoteFunSortCons_isSome hTyTys ▸
    fun (x : (denoteSort ctx.sctx v'.ty).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩) =>
      let v' := { var := v', h := hTy, varΓ := x }
      let vΓ' : TermVarEnvironment ⟨tdi.sΓ, tdi.hsΓ⟩ := v' :: tdi.tΓ.vs
      have hv' : vΓ'.WF vs' :=
        have h' := show _ + _ = _ + _ from tdi.htΓ.hv.h ▸ rfl
        have ha' := fun i hivs => match i with
          | 0 => rfl
          | i + 1 =>
            have hivs' := Nat.lt_of_succ_lt_succ hivs
            have hivΓ := Nat.succ_lt_succ (tdi.htΓ.hv.h ▸ hivs')
            (List.getElem_cons_succ _ ctx.tctx.vs i hivs).symm ▸ (List.getElem_cons_succ _ tdi.tΓ.vs i hivΓ).symm ▸ tdi.htΓ.hv.ha i hivs'
        { h := h', ha := ha' }
      let tdi' : TermDenoteInput ⟨ctx.sctx, tctx'⟩ :=
        { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ, tΓ := { ufs := tdi.tΓ.ufs, vs := vΓ' }, htΓ := { hv := hv', huf := tdi.htΓ.huf } }
      ft' tdi'

noncomputable def buildIFBody (ctx : Context) {hTys hTy}
    (bodyFt : (tdi : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } }) →
              (denoteSort ctx.sctx out).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩)
    (tdi : TermDenoteInput ctx)
    : (denoteFunSort ctx.sctx vs out).get hTys ⟨tdi.sΓ, tdi.hsΓ⟩ :=
    match vs with
    | [] => bodyFt tdi
    | { id := n, ty := ty } :: vs =>
      have hTys' := (denoteFunSortCons_isSome hTys).right
      letI ctx' : Context := { sctx := ctx.sctx, tctx := { vs := { id := n, ty := ty } :: ctx.tctx.vs, ufs := ctx.tctx.ufs } }
      have hvs : ({ id := n, ty := ty } :: vs).reverse ++ ctx.tctx.vs = vs.reverse ++ ctx'.tctx.vs :=
        List.reverse_cons ▸ List.append_assoc _ _ _ ▸ rfl
      let ft' := buildIFBody ctx' (hTys := hTys') (hvs ▸ bodyFt)
      bindIFVar ctx ft' tdi

@[simp]
noncomputable def bindIF {n} {args out} (body : Term) (ctx : Context) (ft' :
    let uf' := { id := n, args := args, out := out }
    let ufs' := uf' :: ctx.tctx.ufs
    let tctx' := { ufs := ufs', vs := ctx.tctx.vs }
    TermDenoteInput ⟨ctx.sctx, tctx'⟩ → Prop) :
  Option (TermDenoteInput ctx → Prop) := do
  if hTys : (denoteFunSort ctx.sctx args out).isSome then
    let bodyCtx : Context := { sctx := ctx.sctx, tctx := { vs := args.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } }
    let ⟨bodyTy, _, bodyFt⟩ ← denoteTerm bodyCtx body
    if hBodyOut : bodyTy = out then
      let uf' := { id := n, args := args, out := out }
      let ufs' := uf' :: ctx.tctx.ufs
      let tctx' : TermContext := { ufs := ufs', vs := ctx.tctx.vs }
      let ft (tdi : TermDenoteInput ctx) :=
        have hBodyOut : denoteSort ctx.sctx out = denoteSort ctx.sctx bodyTy := hBodyOut ▸ rfl
        let f : (denoteFunSort ctx.sctx args out).get hTys ⟨tdi.sΓ, tdi.hsΓ⟩ :=
          buildIFBody ctx (hTy := denoteSortOut_isSome_of_denoteFunSort_isSome hTys) (Option.get_congr hBodyOut ▸ bodyFt) tdi
        let uf' := { uf := uf', h := hTys, ufΓ := f }
        let ufΓ' : UFEnvironment ⟨tdi.sΓ, tdi.hsΓ⟩ := uf' :: tdi.tΓ.ufs
        haveI huf' : ufΓ'.WF ufs' :=
          have h' := show _ + _ = _ + _ from tdi.htΓ.huf.h ▸ rfl
          have ha' := fun i hiufs => match i with
            | 0 => rfl
            | i + 1 =>
              have hiufs' := Nat.lt_of_succ_lt_succ hiufs
              have hiufΓ := Nat.succ_lt_succ (tdi.htΓ.huf.h ▸ hiufs')
              (List.getElem_cons_succ _ ctx.tctx.ufs i hiufs).symm ▸ (List.getElem_cons_succ _ tdi.tΓ.ufs i hiufΓ).symm ▸ tdi.htΓ.huf.ha i hiufs'
          { h := h', ha := ha' }
        let tdi' : TermDenoteInput ⟨ctx.sctx, tctx'⟩ :=
          { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ, tΓ := { ufs := ufΓ', vs := tdi.tΓ.vs }, htΓ := { hv := tdi.htΓ.hv, huf := huf' } }
        ft' tdi'
      return ft
    else
      none
  else
    none

/--
Interpret a boolean term using the bindings defined in an SMT context.
-/
@[simp]
noncomputable def denoteBoolTermFromContext
    (uss : USContext) (iss : ISContext) (ufs : UFContext) (ifs : List Core.SMT.IF) (t : Term) := do
  let ufs := if iss.isEmpty then ufs else ufs.map (substituteUFIS iss)
  let ifs := if iss.isEmpty then ifs else ifs.map (substituteIFIS iss)
  let t := substituteTermIS iss t
  let ⟨.prim .bool, _, ft⟩ ← denoteTerm ⟨⟨uss, iss⟩, ⟨{}, ifs.map Core.SMT.IF.uf ++ ufs⟩⟩ t | none
  let ft ← bindIFs ⟨uss, iss⟩ {} ufs ifs ft
  let ft ← bindUFs ⟨uss, iss⟩ {} ufs ft
  let ft ← bindISs uss iss fun ⟨sΓ, hsΓ⟩ =>
    let tΓ : TermEnvironment ⟨sΓ, hsΓ⟩ := { vs := {}, ufs := {} }
    let htΓ : tΓ.WF { vs := {}, ufs := {} } :=
      { hv := { h := rfl, ha := fun _ hi => nomatch hi },
        huf := { h := rfl, ha := fun _ hi => nomatch hi } }
    ft { sΓ, hsΓ, tΓ, htΓ }
  let ft ← bindUSs uss [] ft
  let sΓ : SortEnvironment := {}
  let hsΓ : sΓ.WF {} := { h := rfl, ha := fun _ hi => nomatch hi }
  return PLift.up (ft { sΓ, hsΓ })
where
  @[simp]
  bindUSs uss iss (ft' : SortDenoteInput ⟨uss, iss⟩ → Prop) : Option (SortDenoteInput ⟨[], iss⟩ → Prop) :=
    do match uss with
    | [] => return ft'
    | _ :: uss =>
      let ft ← bindUS uss iss ft'
      bindUSs uss iss ft
  @[simp]
  bindISs uss iss (ft' : SortDenoteInput ⟨uss, iss⟩ → Prop) : Option (SortDenoteInput ⟨uss, []⟩ → Prop) :=
    return fun (tdi : SortDenoteInput ⟨uss, []⟩) => ft' ⟨tdi.sΓ, tdi.hsΓ⟩
  @[simp]
  bindUFs sctx vs ufs (ft' : TermDenoteInput ⟨sctx, ⟨vs, ufs⟩⟩ → Prop) : Option (TermDenoteInput ⟨sctx, ⟨vs, []⟩⟩ → Prop) :=
    do match ufs with
    | [] => return ft'
    | _ :: ufs =>
      let ft ← bindUF { sctx, tctx := { vs, ufs } } ft'
      bindUFs sctx vs ufs ft
  @[simp]
  bindIFs sctx vs ufs (ifs : List _) (ft' : TermDenoteInput ⟨sctx, ⟨vs, ifs.map Core.SMT.IF.uf ++ ufs⟩⟩ → Prop) :
      Option (TermDenoteInput ⟨sctx, ⟨vs, ufs⟩⟩ → Prop) :=
    do match ifs with
    | [] => return ft'
    | { uf := _, body } :: ifs =>
      let ft ← bindIF body { sctx, tctx := { vs := vs, ufs := ifs.map Core.SMT.IF.uf ++ ufs } } ft'
      bindIFs sctx vs ufs ifs ft

def mkISContext (iss : Map String TermType) : ISContext :=
  go {} iss
where
  go (isctx : ISContext) : Map String TermType → ISContext
  | [] => isctx
  | (n, ty) :: iss => go ((n, substituteIS isctx ty) :: isctx) iss

/--
Interpret an SMT query by universally quantifying assumptions and returning the semantic proposition.
-/
@[simp]
noncomputable def denoteQuery (ctx : Core.SMT.Context) (assums : List Term) (conc : Term) : Option Prop := do
  -- Datatypes not supported yet
  if !ctx.typeFactory.isEmpty || !ctx.seenDatatypes.isEmpty || !ctx.datatypeFuns.isEmpty then none
  let stmt := assums.foldr (.app .implies [·, ·] (.prim .bool)) conc
  let t := ctx.axms.foldr (.app .implies [·, ·] (.prim .bool)) stmt
  let uss := ctx.sorts.toList.reverse
  let iss := (mkISContext ctx.tySubst).reverse
  let ufs := ctx.ufs.toList.reverse
  let ifs := ctx.ifs.toList.reverse
  (denoteBoolTermFromContext uss iss ufs ifs t).map PLift.down

#reduce denoteIntTermAux (.app .add [.prim (.int 1), .prim (.int 2)] (.prim .int))
#reduce (types := true) denoteBoolTermAux (.app .lt [.prim (.int 1), .prim (.int 2)] (.prim .int))
-- #reduce (types := true) let a := { id := "a", ty := .prim .int }
  -- (denoteBoolTermAux (.quant .all [a] a (.app .gt [.prim (.int 42), a] (.prim .int))))

example :
  let a := { id := "a", ty := .prim .int }
  (denoteBoolTermAux (.quant .all [a] a (.app .gt [.prim (.int 42), a] (.prim .int)))) =
  .some (∀ (x : Int), 42 > x) := by
  rfl

example :
  let a := { id := "a", ty := .prim (.bitvec 32) }
  (denoteQuery {} [] (.quant .all [a] a (.app .bvugt [.prim (.bitvec (42 : BitVec 32)), a] (.prim (.bitvec 32))))) =
  .some (∀ (x : BitVec 32), 42 > x) := by
  rfl

example :
  let a := { id := "a", args := [],  out := .prim (.bitvec 32) }
  let b := { id := "b", args := [],  out := .prim (.bitvec 16) }
  (denoteQuery { ufs := #[a, b] } []
    (.app .eq [.app .bvconcat [.app (.uf a) [] a.out, .app (.uf b) [] b.out] (.prim (.bitvec 48)),
               .app .bvconcat [.app (.uf b) [] b.out, .app (.uf a) [] a.out] (.prim (.bitvec 48))] (.prim .bool))) =
  .some (∀ (x : BitVec 32) (y : BitVec 16), x ++ y = y ++ x) := by
  rfl

example :
  let α := { name := "α", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [] }
  (denoteQuery { sorts := #[α], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type) [Nonempty α] (x : α), x = x) := by
  rfl

example :
  let α := { name := "α", arity := 1 }
  let a := { id := "a", args := [],  out := .constr α.name [.prim .int] }
  (denoteQuery { sorts := #[α], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type) [∀ x, Nonempty (α x)] (x : α Int), x = x) := by
  rfl

example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [.constr β.name [], .prim .bool] }
  (denoteQuery { sorts := #[α, β], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ x y, Nonempty (α x y)] (β : Type) [Nonempty β] (x : α β Prop), x = x) := by
  rfl

example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let γ := ("γ", .constr α.name [.constr β.name [], .prim .bool])
  let a := { id := "a", args := [],  out := .constr γ.fst [] }
  (denoteQuery { sorts := #[α, β], ufs := #[a], tySubst := [γ] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ (x y : Type), Nonempty (α x y)] (β : Type) [Nonempty β],
         let γ := α β Prop
         ∀ (a : γ), a = a) := by
  rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .constr α.fst [] }
  (denoteQuery { ufs := #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (a : α), ¬a) := by
  rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .prim .bool }
  (denoteQuery { ufs := #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (a : α), ¬a) := by
  rfl

example :
  let a := { id := "a", args := [],  out := .prim .int }
  (denoteQuery { ufs := #[a] } [] (.app .gt [.prim (.int 42), .app (.uf a) [] a.out] (.prim .int))) =
  .some (∀ (x : Int), 42 > x) := by
  rfl

example :
  let a := { id := "a", args := [], out := .prim .int }
  (denoteQuery {ufs := #[a]} [] (.app .gt [.prim (.int 42), .app (.uf a) [] (.prim .int)] (.prim .int))) =
  .some (∀ (x : Int), 42 > x) := by
  rfl

example :
  let f := { id := "f", args := [{ id := "a", ty := .prim .int }], out := .prim .int }
  let f3 := .app (.uf f) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ufs := #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (∀ (f : Int → Int), 42 > f 3) := by
  rfl

example :
  let a := { id := "a", ty := .prim .int }
  let f := { uf := { id := "f", args := [a], out := .prim .int }, body := .app .add [.var a, .prim (.int 2)] (.prim .int) }
  let f3 := .app (.uf f.uf) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ifs := #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (let f (a : Int) := a + 2; 42 > f 3) := by
  rfl

example :
  let ctx := {
      sorts := #[],
      ufs := #[{ id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }],
      ifs := #[],
      axms := #[],
      tySubst := [] }
  let ts := [Term.app
       (Op.lt)
       [Term.prim (TermPrim.int 0),
        Term.app
          (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int))]
       (TermType.prim (TermPrimType.bool)),
     Term.app
       (Op.ge)
       [Term.app
          (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int)),
        Term.prim (TermPrim.int 0)]
       (TermType.prim (TermPrimType.bool))]
  let t := Term.app
      (Op.and)
      [Term.app
         (Op.le)
         [Term.prim (TermPrim.int 0),
          Term.app
            (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int))]
         (TermType.prim (TermPrimType.bool)),
       Term.prim (TermPrim.bool true)]
      (TermType.prim (TermPrimType.bool))
  (denoteQuery ctx ts t) =
  .some (∀ («$__n0» : Int), 0 < «$__n0» → «$__n0» ≥ 0 → 0 ≤ «$__n0» ∧ True) := by
  rfl
