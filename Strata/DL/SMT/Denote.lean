/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder

public section

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

@[expose] def mkTypeFunType (n : Nat) : Type 1 := n.repeat (Type → ·) Type

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

@[reducible] def applyNonemptyPred {n : Nat} {fα : mkTypeFunType n} (hfα : mkNonemptyPred fα) (αs : List Type) (h : αs.length = n) :
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

/-- Interpret primitive SMT types as Lean types, when supported. -/
@[expose] def denotePrimSort (sctx : SortContext) (pty : TermPrimType) : Option (SortDenoteResult sctx) := do
  match pty with
  | .bool => return fun _ => Prop
  | .int => return fun _ => Int
  | .bitvec n => return fun _ => BitVec n
  -- We don't have access to `Real` in `Strata`, so we leave it as `none` for now.
  | .real => none -- fin _ => Real
  | .string => return fun _ => String
  | .regex => none
  | .trigger => none

/--
Interpret an SMT `TermType` as a Lean `Type`, when supported.

Returns `none` when we lack an interpretation (e.g. for reals).

Note: similar to `denoteSort`, but does not attempt to look up type synonyms.
-/
def denoteSortAux (sctx : SortContext) (ty : TermType) : Option (SortDenoteResult sctx) := do
  match ty with
  | .prim pty => denotePrimSort sctx pty
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
@[expose] def denoteSort (sctx : SortContext) (ty : TermType) : Option (SortDenoteResult sctx) := do
  match ty with
  | .prim pty => denotePrimSort sctx pty
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

/-- Forget semantic values, keeping only the declared term variables. -/
def TermVarEnvironment.toContext (tΓ : TermVarEnvironment sΓ) : TermVarContext :=
  tΓ.map (·.var)

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

/-- Forget semantic values, keeping only UF declarations. -/
def UFEnvironment.toContext (Γ : UFEnvironment sΓ) : UFContext :=
  Γ.map (·.uf)

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

This is intentionally separate from `TermEnvironment`: an environment contains
strictly more information (semantic values), but denotation judgments are
formulated against syntax-level declarations and then related to environments
via `TermEnvironment.WF`.
-/
structure TermContext where
  vs  : TermVarContext := []
  ufs : UFContext := []

/--
Semantic environment providing Lean values for the elements stored in a
`TermContext`.

Although this could project back to a context (`toContext`), we keep an
explicit `TermContext` parameter in denotation APIs so binder-extension and
lookup steps can be stated over declarations first, with realizability tracked
separately via `WF`.
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
Check that denoted argument types match declared variable types.

If lengths differ, this returns `false`.
-/
@[simp, expose]
noncomputable def argTypesAlign (as : List (TermDenoteResult ctx)) (vs : List TermVar) : Bool :=
  match as, vs with
  | [], [] => true
  | a :: as, v :: vs =>
    a.ty == v.ty && argTypesAlign as vs
  | _, _ => false

private theorem argTypesAlign_true_with_len (h : argTypesAlign as vs) (hl : as.length = vs.length) :
  ∀ i, (h : i < as.length) → as[i].ty = (vs[i]'(hl ▸ h)).ty := fun i hi =>
  match as, vs with
  | [], _ => nomatch h
  | _ :: _, [] =>
    False.elim (by simp at hl)
  | a :: as, v :: vs =>
    match i with
    | 0 => eq_of_beq (Bool.and_eq_true_iff.mp h).left
    | i + 1 =>
      (List.getElem_cons_succ a as i hi).symm ▸ (List.getElem_cons_succ v vs i (hl ▸ hi)).symm ▸
      argTypesAlign_true_with_len (Bool.and_eq_true_iff.mp h).right (Nat.succ.inj hl) i (Nat.lt_of_succ_lt_succ hi)

theorem argTypesAlign_length_eq (h : argTypesAlign as vs) : as.length = vs.length := by
  match as, vs with
  | [], [] => rfl
  | [], _ :: _ => contradiction
  | _ :: _, [] => contradiction
  | _ :: as, _ :: vs =>
    have h' : as.length = vs.length := argTypesAlign_length_eq (Bool.and_eq_true_iff.mp h).right
    simpa using congrArg Nat.succ h'

theorem argTypesAlign_true {as : List (TermDenoteResult ctx)} {vs : List TermVar} (h : argTypesAlign as vs) :
  ∀ i, (hi : i < as.length) → as[i].ty = (vs[i]'(argTypesAlign_length_eq h ▸ hi)).ty :=
  argTypesAlign_true_with_len h (argTypesAlign_length_eq h)

theorem argTypesAlign_arg_types {as : List (TermDenoteResult ctx)} {vs : List TermVar} (h : argTypesAlign as vs) :
  ∀ i, (hi : i < as.length) → as[i].ty = (vs[i]'(argTypesAlign_length_eq h ▸ hi)).ty :=
  argTypesAlign_true h

-- Note: `noncomputable` because of a compiler error
/--
Apply the semantic interpretation of a UF symbol to denoted arguments.
-/
@[simp]
noncomputable def applyUFAux (tdi : TermDenoteInput ctx) (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
  (as : List (TermDenoteResult ctx)) (hl : args.length = as.length) (has : ∀ i, (hi : i < as.length) → as[i].ty = (args[i]'(hl ▸ hi)).ty) :
    (denoteSort ctx.sctx out).get (denoteSortOut_isSome_of_denoteFunSort_isSome h) ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  match args, as with
  | [], []            => uf
  | arg :: _, a :: as =>
    let uf := arrow_of_denoteFunSortCons_isSome h ▸ uf
    have ha : denoteSort ctx.sctx arg.ty = denoteSort ctx.sctx a.ty := has 0 (Nat.zero_lt_succ _) ▸ rfl
    let uf := uf (Option.get_congr ha ▸ a.res tdi)
    applyUFAux tdi uf as (Nat.succ.inj hl) (fun i hi => (has (i + 1) (Nat.succ_lt_succ hi)))

/--
Apply the semantic interpretation of a UF symbol to denoted arguments.
-/
@[simp]
noncomputable def applyUF (tdi : TermDenoteInput ctx) (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
  (as : List (TermDenoteResult ctx)) (hAlign : argTypesAlign as args) :
    (denoteSort ctx.sctx out).get (denoteSortOut_isSome_of_denoteFunSort_isSome h) ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  applyUFAux tdi uf as (argTypesAlign_length_eq hAlign).symm (argTypesAlign_arg_types hAlign)

/--
Shape of a one-variable quantifier binder combinator (`∀` or `∃`).
-/
abbrev QuantVarBinder :=
  {n : String} → {ty : TermType} → (ctx : Context) →
    (hTy : (denoteSort ctx.sctx ty).isSome) →
      let tctx := { ufs := ctx.tctx.ufs, vs := ctx.tctx.vs }
      let v' := { id := n, ty := ty }
      let vs' := v' :: ctx.tctx.vs
      let tctx' := { ufs := ctx.tctx.ufs, vs := vs' }
      (TermDenoteInput ⟨ctx.sctx, tctx'⟩ → Prop) →
      TermDenoteInput ⟨ctx.sctx, tctx⟩ → Prop

/--
Semantics helper for universal quantification.

Given a body interpretation over the context extended with one bound variable
`(n : ty)`, produce the interpretation in the original context by universally
quantifying over all Lean values of the denoted sort `ty`. This also extends
the term environment with the chosen value and carries the corresponding `WF`
proof for the extended context.
-/
@[simp]
def bindForallVar : QuantVarBinder := fun {n} {ty} ctx hTy =>
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

/--
Semantics helper for existential quantification.

Given a body interpretation over the context extended with one bound variable
`(n : ty)`, produce the interpretation in the original context by existentially
quantifying over Lean values of the denoted sort `ty`. This also extends the
term environment with the chosen witness and carries the corresponding `WF`
proof for the extended context.
-/
@[simp]
def bindExistsVar : QuantVarBinder := fun {n} {ty} ctx hTy =>
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

def buildQuant (bindVar : QuantVarBinder) (ctx : Context) (vs : List TermVar)
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
      let ft' := buildQuant bindVar ctx' vs hTys' (hvs ▸ bodyFt)
      bindVar (n := n) (ty := ty) ctx (denoteFunSortCons_isSome hTys).left ft' tdi

def buildExists (ctx : Context) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome)
    (bodyFt : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (tdi : TermDenoteInput ctx)
    : Prop :=
  buildQuant bindExistsVar ctx vs hTys bodyFt tdi

def buildForall (ctx : Context) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx vs (.prim .bool)).isSome)
    (bodyFt : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (tdi : TermDenoteInput ctx)
    : Prop :=
  buildQuant bindForallVar ctx vs hTys bodyFt tdi

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
  -- Variable lookup: if `v` is declared in `ctx.tctx.vs` and its sort can be
  -- interpreted, return the corresponding semantic value from `tdi.tΓ.vs`.
  -- The proof terms below only transport this value across context/WF equalities.
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
  -- UF application: lookup the UF symbol in `ctx.tctx.ufs`, denote arguments,
  -- check argument-type alignment, then apply the UF interpretation from
  -- `tdi.tΓ.ufs` to the denoted arguments.
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
              (Option.get_congr hufΓ ▸ tdi.tΓ.ufs[i].ufΓ) as hufas
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

/--
Interpret a ground bitvector term in the empty context.
-/
@[simp]
noncomputable def denoteBVTermAux (n : Nat) (t : Term) : Option (BitVec n) := do
  let some ⟨.prim (.bitvec m), _, fi⟩ := denoteTerm {} t | none
  if h : m = n then
    return h ▸ fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, ⟨[], []⟩, ⟨{ h := rfl, ha := fun _ hi => nomatch hi }, { h := rfl, ha := fun _ hi => nomatch hi }⟩⟩
  else
    none

/--
Interpret a ground string term in the empty context.
-/
@[simp]
noncomputable def denoteStringTermAux (t : Term) : Option String := do
  let some ⟨.prim .string, _, fi⟩ := denoteTerm {} t | none
  return fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, ⟨[], []⟩, ⟨{ h := rfl, ha := fun _ hi => nomatch hi }, { h := rfl, ha := fun _ hi => nomatch hi }⟩⟩

/--
Eliminate one uninterpreted sort binder by quantifying over all of its
semantic realizations and extending the sort environment accordingly.
-/
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

/--
Lambda-lift one IF-body argument binder into an arrow in the resulting function.
-/
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

/--
Turn a denoted IF body (under its argument binders) into a denoted function.
-/
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

/--
Eliminate one interpreted-function declaration from the term context.

`ft'` expects a context where the function symbol `(n : args -> out)` is
available in `tctx.ufs`. This combinator constructs the semantic function by
denoting `body`, pushes that interpretation into the environment, and returns a
proposition over the original (smaller) context.
-/
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
Interpret a closed boolean term under SMT declarations.

`denoteTerm` is context-parametric: it interprets a term relative to explicit
sort/term contexts and semantic environments. This function "closes" that
interpretation by successively eliminating context binders (`IF`, `UF`, sort
aliases, uninterpreted sorts) and then evaluating in the empty environment.

It is boolean-specific because SMT queries denote propositions.
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
  /--
  Eliminate all uninterpreted sort binders by repeatedly applying `bindUS`.
  -/
  @[simp]
  bindUSs uss iss (ft' : SortDenoteInput ⟨uss, iss⟩ → Prop) : Option (SortDenoteInput ⟨[], iss⟩ → Prop) :=
    do match uss with
    | [] => return ft'
    | _ :: uss =>
      let ft ← bindUS uss iss ft'
      bindUSs uss iss ft
  /--
  Eliminate interpreted-sort aliases. They are already substituted, so this
  step only reindexes the context shape.
  -/
  @[simp]
  bindISs uss iss (ft' : SortDenoteInput ⟨uss, iss⟩ → Prop) : Option (SortDenoteInput ⟨uss, []⟩ → Prop) :=
    return fun (tdi : SortDenoteInput ⟨uss, []⟩) => ft' ⟨tdi.sΓ, tdi.hsΓ⟩
  /--
  Eliminate all uninterpreted-function binders by repeatedly applying `bindUF`.
  -/
  @[simp]
  bindUFs sctx vs ufs (ft' : TermDenoteInput ⟨sctx, ⟨vs, ufs⟩⟩ → Prop) : Option (TermDenoteInput ⟨sctx, ⟨vs, []⟩⟩ → Prop) :=
    do match ufs with
    | [] => return ft'
    | _ :: ufs =>
      let ft ← bindUF { sctx, tctx := { vs, ufs } } ft'
      bindUFs sctx vs ufs ft
  /--
  Eliminate all interpreted-function declarations by repeatedly applying `bindIF`.
  -/
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

/-! ## Inductive denotation predicate for ground terms

`DenotePred t v` holds when the ground (closed, quantifier-free) SMT term `t`
evaluates to the primitive value `v`. Unlike the functional denotation
`denoteTerm`, which threads contexts and environments through a
dependently-typed interpreter, `DenotePred` is a plain inductive family
`Term → TermPrim → Prop` that admits straightforward structural induction.

### Coverage

The predicate currently covers binary applications of all operators handled by
`denoteTerm`.  N-ary (left- and right-associative, chainable) applications can
be reduced to binary form; additional constructors for n-ary patterns may be
added as needed.

### Equivalence

`DenotePred.sound_bool` and `DenotePred.sound_int` relate the predicate to the
functional denotation (`denoteBoolTermAux`, `denoteIntTermAux`).
-/

/-- Inductive predicate relating a ground SMT `Term` to the `TermPrim` it
    denotes.  Each constructor corresponds to one evaluation rule from
    `denoteTerm` restricted to the ground, quantifier-free, binary fragment. -/
inductive DenotePred : Term → TermPrim → Prop where
  -- ═══ Literals ═══
  -- Split by type (excluding `.real` which `denoteTerm` does not support).
  /-- A boolean literal. -/
  | prim_bool (b : Bool) : DenotePred (.prim (.bool b)) (.bool b)
  /-- An integer literal. -/
  | prim_int (n : Int) : DenotePred (.prim (.int n)) (.int n)
  /-- A bitvector literal. -/
  | prim_bitvec {n : Nat} (x : BitVec n) : DenotePred (.prim (.bitvec x)) (.bitvec x)
  /-- A string literal. -/
  | prim_string (s : String) : DenotePred (.prim (.string s)) (.string s)
  -- ═══ Core boolean operations ═══
  /-- Boolean negation. -/
  | not {a : Term} {b : Bool} {ty : TermType} :
      DenotePred a (.bool b) →
      DenotePred (.app .not [a] ty) (.bool (!b))
  /-- Binary conjunction. -/
  | and {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .and [a, b] ty) (.bool (ba && bb))
  /-- Binary disjunction. -/
  | or {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .or [a, b] ty) (.bool (ba || bb))
  /-- Binary implication (`=>` in SMT-LIB). -/
  | implies {a b : Term} {ba bb : Bool} {ty : TermType} :
      DenotePred a (.bool ba) → DenotePred b (.bool bb) →
      DenotePred (.app .implies [a, b] ty) (.bool ((!ba) || bb))
  /-- Equality of two same-type values (uses decidable equality on `TermPrim`). -/
  | eq {a b : Term} {va vb : TermPrim} {ty : TermType} :
      DenotePred a va → DenotePred b vb →
      va.typeOf = vb.typeOf →
      DenotePred (.app .eq [a, b] ty) (.bool (decide (va = vb)))
  /-- If-then-else, true branch (both branches must be denotable with matching types). -/
  | ite_true {c a b : Term} {ty : TermType} {v vb : TermPrim} :
      DenotePred c (.bool true) → DenotePred a v → DenotePred b vb →
      v.typeOf = vb.typeOf →
      DenotePred (.app .ite [c, a, b] ty) v
  /-- If-then-else, false branch (both branches must be denotable with matching types). -/
  | ite_false {c a b : Term} {ty : TermType} {va v : TermPrim} :
      DenotePred c (.bool false) → DenotePred a va → DenotePred b v →
      va.typeOf = v.typeOf →
      DenotePred (.app .ite [c, a, b] ty) v
  -- ═══ Integer arithmetic ═══
  /-- Integer negation. -/
  | neg_int {a : Term} {n : Int} {ty : TermType} :
      DenotePred a (.int n) →
      DenotePred (.app .neg [a] ty) (.int (-n))
  /-- Binary integer addition. -/
  | add_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .add [a, b] ty) (.int (na + nb))
  /-- Binary integer subtraction. -/
  | sub_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .sub [a, b] ty) (.int (na - nb))
  /-- Binary integer multiplication. -/
  | mul_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .mul [a, b] ty) (.int (na * nb))
  /-- Binary integer division (Lean semantics: `x / 0 = 0`). -/
  | div_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .div [a, b] ty) (.int (na / nb))
  /-- Integer modulus (Lean semantics: `x % 0 = x`). -/
  | mod_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .mod [a, b] ty) (.int (na % nb))
  /-- Integer absolute value. -/
  | abs_int {a : Term} {n : Int} {ty : TermType} :
      DenotePred a (.int n) →
      DenotePred (.app .abs [a] ty) (.int (if n < 0 then -n else n))
  -- ═══ Integer comparisons ═══
  /-- Integer `≤`. -/
  | le_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .le [a, b] ty) (.bool (decide (na ≤ nb)))
  /-- Integer `<`. -/
  | lt_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .lt [a, b] ty) (.bool (decide (na < nb)))
  /-- Integer `≥`. -/
  | ge_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .ge [a, b] ty) (.bool (decide (na ≥ nb)))
  /-- Integer `>`. -/
  | gt_int {a b : Term} {na nb : Int} {ty : TermType} :
      DenotePred a (.int na) → DenotePred b (.int nb) →
      DenotePred (.app .gt [a, b] ty) (.bool (decide (na > nb)))
  -- ═══ Bitvector arithmetic ═══
  /-- Bitvector negation. -/
  | bvneg {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvneg [a] ty) (.bitvec (-x))
  /-- Binary bitvector addition. -/
  | bvadd {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvadd [a, b] ty) (.bitvec (x + y))
  /-- Binary bitvector subtraction. -/
  | bvsub {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsub [a, b] ty) (.bitvec (x - y))
  /-- Binary bitvector multiplication. -/
  | bvmul {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvmul [a, b] ty) (.bitvec (x * y))
  /-- Bitvector bitwise NOT. -/
  | bvnot {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvnot [a] ty) (.bitvec (~~~x))
  /-- Binary bitvector AND. -/
  | bvand {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvand [a, b] ty) (.bitvec (x &&& y))
  /-- Binary bitvector OR. -/
  | bvor {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvor [a, b] ty) (.bitvec (x ||| y))
  /-- Binary bitvector XOR. -/
  | bvxor {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvxor [a, b] ty) (.bitvec (x ^^^ y))
  /-- Bitvector shift left (operands may have different widths). -/
  | bvshl {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvshl [a, b] ty) (.bitvec (x <<< y))
  /-- Bitvector logical shift right (operands may have different widths). -/
  | bvlshr {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvlshr [a, b] ty) (.bitvec (x >>> y))
  /-- Bitvector arithmetic shift right (operands may have different widths). -/
  | bvashr {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvashr [a, b] ty) (.bitvec (BitVec.sshiftRight' x y))
  -- ═══ Bitvector comparisons (same width) ═══
  /-- Bitvector signed `<`. -/
  | bvslt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvslt [a, b] ty) (.bool (BitVec.slt x y))
  /-- Bitvector signed `≤`. -/
  | bvsle {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsle [a, b] ty) (.bool (BitVec.sle x y))
  /-- Bitvector unsigned `<`. -/
  | bvult {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvult [a, b] ty) (.bool (decide (x < y)))
  /-- Bitvector unsigned `≤`. -/
  | bvule {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvule [a, b] ty) (.bool (decide (x ≤ y)))
  /-- Bitvector signed `>`. -/
  | bvsgt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsgt [a, b] ty) (.bool (BitVec.slt y x))
  /-- Bitvector signed `≥`. -/
  | bvsge {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsge [a, b] ty) (.bool (BitVec.sle y x))
  /-- Bitvector unsigned `>`. -/
  | bvugt {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvugt [a, b] ty) (.bool (decide (x > y)))
  /-- Bitvector unsigned `≥`. -/
  | bvuge {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvuge [a, b] ty) (.bool (decide (x ≥ y)))
  -- ═══ Bitvector division / remainder ═══
  /-- Bitvector unsigned division (same width, SMT-LIB semantics). -/
  | bvudiv {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvudiv [a, b] ty) (.bitvec (BitVec.smtUDiv x y))
  /-- Bitvector unsigned remainder (same width). -/
  | bvurem {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvurem [a, b] ty) (.bitvec (x % y))
  /-- Bitvector signed division (same width, SMT-LIB semantics). -/
  | bvsdiv {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsdiv [a, b] ty) (.bitvec (BitVec.smtSDiv x y))
  /-- Bitvector signed remainder (same width). -/
  | bvsrem {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsrem [a, b] ty) (.bitvec (BitVec.srem x y))
  -- ═══ Bitvector overflow predicates ═══
  /-- Bitvector negation overflow. -/
  | bvnego {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) →
      DenotePred (.app .bvnego [a] ty) (.bool (BitVec.negOverflow x))
  /-- Bitvector signed addition overflow (same width). -/
  | bvsaddo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsaddo [a, b] ty) (.bool (BitVec.saddOverflow x y))
  /-- Bitvector signed subtraction overflow (same width). -/
  | bvssubo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvssubo [a, b] ty) (.bool (BitVec.ssubOverflow x y))
  /-- Bitvector signed multiplication overflow (same width). -/
  | bvsmulo {a b : Term} {n : Nat} {x y : BitVec n} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvsmulo [a, b] ty) (.bool (BitVec.smulOverflow x y))
  -- ═══ Bitvector concatenation and extension ═══
  /-- Bitvector concatenation. -/
  | bvconcat {a b : Term} {n m : Nat} {x : BitVec n} {y : BitVec m} {ty : TermType} :
      DenotePred a (.bitvec x) → DenotePred b (.bitvec y) →
      DenotePred (.app .bvconcat [a, b] ty) (.bitvec (x ++ y))
  /-- Bitvector zero extension by `i` bits. -/
  | zero_extend {a : Term} {n : Nat} {x : BitVec n} {ty : TermType} (i : Nat) :
      DenotePred a (.bitvec x) →
      DenotePred (.app (.zero_extend i) [a] ty) (.bitvec (BitVec.zeroExtend (n + i) x))
  -- ═══ String operations ═══
  /-- String length (result is a non-negative integer). -/
  | str_length {s : Term} {sv : String} {ty : TermType} :
      DenotePred s (.string sv) →
      DenotePred (.app .str_length [s] ty) (.int (Int.ofNat sv.length))
  /-- Binary string concatenation. -/
  | str_concat {a b : Term} {sa sb : String} {ty : TermType} :
      DenotePred a (.string sa) → DenotePred b (.string sb) →
      DenotePred (.app .str_concat [a, b] ty) (.string (sa ++ sb))

/-! ### Soundness proof infrastructure -/

/-- The unique `TermDenoteInput` for the empty context. -/
private noncomputable abbrev tdi₀ : TermDenoteInput ({} : Context) :=
  ⟨[], ⟨rfl, fun _ hi => nomatch hi⟩, ⟨[], []⟩,
   ⟨⟨rfl, fun _ hi => nomatch hi⟩, ⟨rfl, fun _ hi => nomatch hi⟩⟩⟩

/-- Soundness goal for each `TermPrim` variant.  Tracks the `denoteTerm`
    result so that the induction hypothesis is usable across type boundaries
    (e.g. integer sub-terms inside boolean comparisons). -/
private noncomputable def DenotePred.SoundGoal (t : Term) : TermPrim → Prop
  | .bool b         => ∃ f : TermDenoteInput ({} : Context) → Prop,
                          denoteTerm ({} : Context) t = some ⟨.prim .bool, rfl, f⟩ ∧ (f tdi₀ ↔ b = true)
  | .int n          => ∃ f : TermDenoteInput ({} : Context) → Int,
                          denoteTerm ({} : Context) t = some ⟨.prim .int, rfl, f⟩ ∧ f tdi₀ = n
  | @TermPrim.bitvec k x => ∃ f : TermDenoteInput ({} : Context) → BitVec k,
                          denoteTerm ({} : Context) t = some ⟨.prim (.bitvec k), rfl, f⟩ ∧ f tdi₀ = x
  | .string s       => ∃ f : TermDenoteInput ({} : Context) → String,
                          denoteTerm ({} : Context) t = some ⟨.prim .string, rfl, f⟩ ∧ f tdi₀ = s
  | .real _         => True

/-- No `DenotePred` derivation produces a `.real` value (reals are unsupported by `denoteTerm`). -/
private theorem DenotePred.not_real {t : Term} {v : TermPrim} (h : DenotePred t v) :
    ∀ d : Strata.Decimal, v = .real d → False := by
  induction h <;> intro d heq <;> simp_all [TermPrim.typeOf]

/-! ### Core soundness lemma -/

private theorem DenotePred.sound_aux {t : Term} {v : TermPrim} (h : DenotePred t v) :
    DenotePred.SoundGoal t v := by
  induction h with
  -- ═══ Literals ═══
  | prim_bool b =>
    unfold SoundGoal; cases b
    all_goals exact ⟨_, by unfold denoteTerm; rfl, by simp⟩
  | prim_int n => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  | prim_bitvec x => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  | prim_string s => exact ⟨_, by unfold denoteTerm; rfl, rfl⟩
  -- ═══ Core boolean operations ═══
  | @not _ b _ _ ih =>
    obtain ⟨f, hdt, hiff⟩ := ih
    refine ⟨fun Γ => ¬f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, ?_⟩
    cases b <;> simp_all
  | @and _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ ∧ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    constructor
    · rintro ⟨ha, hb⟩; rw [Bool.and_eq_true]; exact ⟨hiffa.mp ha, hiffb.mp hb⟩
    · intro h; rw [Bool.and_eq_true] at h; exact ⟨hiffa.mpr h.1, hiffb.mpr h.2⟩
  | @or _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ ∨ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    constructor
    · rintro (ha | hb)
      · rw [Bool.or_eq_true]; exact Or.inl (hiffa.mp ha)
      · rw [Bool.or_eq_true]; exact Or.inr (hiffb.mp hb)
    · intro h; rw [Bool.or_eq_true] at h; exact h.elim (Or.inl ∘ hiffa.mpr) (Or.inr ∘ hiffb.mpr)
  | @implies _ _ ba bb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
    refine ⟨fun Γ => fa Γ → fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms rightAssoc rightAssoc.go; rw [hdta, hdtb]; first | rfl | simp, ?_⟩
    cases ba <;> cases bb <;> simp_all
  | @eq _ _ va vb _ ha _ htyeq iha ihb =>
    cases va with
    | real d => exact absurd rfl (DenotePred.not_real ha d)
    | bool ba =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | bool bb =>
        obtain ⟨fa, hdta, hiffa⟩ := iha; obtain ⟨fb, hdtb, hiffb⟩ := ihb
        refine ⟨fun Γ => fa Γ ↔ fb Γ,
          by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
             simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                        dite_true]
             congr; funext x; apply propext; exact eq_iff_iff, ?_⟩
        simp only [decide_eq_true_eq]
        cases ba <;> cases bb <;> simp_all
      | int _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | int na =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | int nb =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | @bitvec ka xa =>
      cases vb with
      | real _ => simp [TermPrim.typeOf] at htyeq
      | @bitvec kb xb =>
        have hkk : ka = kb := by
          simp only [TermPrim.typeOf, TermType.bitvec] at htyeq
          injection htyeq with h; injection h
        subst hkk
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | int _ => simp [TermPrim.typeOf] at htyeq
      | string _ => simp [TermPrim.typeOf] at htyeq
    | string sa =>
      cases vb with
      | string sb =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => fa Γ = fb Γ, ?_, ?_⟩
        · unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go
          simp only [hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [hvala, hvalb, decide_eq_true_eq]
      | real _ => simp [TermPrim.typeOf] at htyeq
      | bool _ => simp [TermPrim.typeOf] at htyeq
      | int _ => simp [TermPrim.typeOf] at htyeq
      | bitvec _ => simp [TermPrim.typeOf] at htyeq
  | @ite_true _ _ _ _ v vb _ _ _ htyeq ihc iha ihb =>
    obtain ⟨fc, hdtc, hiffc⟩ := ihc
    have hcpos : fc tdi₀ := hiffc.mpr rfl
    cases v with
    | real _ => trivial
    | bool b =>
      cases vb with
      | bool _ =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp only [if_pos hcpos]; exact hvala
      | _ => simp [TermPrim.typeOf] at htyeq
    | int n =>
      cases vb with
      | int _ =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_pos hcpos]; exact hvala
      | _ => simp [TermPrim.typeOf] at htyeq
    | @bitvec k x =>
      cases vb with
      | @bitvec k' _ =>
        have hk : k = k' := by simp [TermPrim.typeOf] at htyeq; exact htyeq
        subst hk
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_pos hcpos]; exact hvala
      | _ => simp [TermPrim.typeOf] at htyeq
    | string s =>
      cases vb with
      | string _ =>
        obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, _⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_pos hcpos]; exact hvala
      | _ => simp [TermPrim.typeOf] at htyeq
  | @ite_false _ _ _ _ va v _ _ _ htyeq ihc iha ihb =>
    obtain ⟨fc, hdtc, hiffc⟩ := ihc
    have hcneg : ¬fc tdi₀ := fun h => by simp at hiffc; exact hiffc h
    cases v with
    | real _ => trivial
    | bool b =>
      cases va with
      | bool _ =>
        obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp only [if_neg hcneg]; exact hvalb
      | _ => simp [TermPrim.typeOf] at htyeq
    | int n =>
      cases va with
      | int _ =>
        obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_neg hcneg]; exact hvalb
      | _ => simp [TermPrim.typeOf] at htyeq
    | @bitvec k x =>
      cases va with
      | @bitvec k' _ =>
        have hk : k' = k := by simp [TermPrim.typeOf] at htyeq; exact htyeq
        subst hk
        obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_neg hcneg]; exact hvalb
      | _ => simp [TermPrim.typeOf] at htyeq
    | string s =>
      cases va with
      | string _ =>
        obtain ⟨fa, hdta, _⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
        refine ⟨fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ), ?_, ?_⟩
        · unfold denoteTerm
          simp only [hdtc, hdta, hdtb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                     dite_true]
          congr; funext
        · simp [if_neg hcneg]; exact hvalb
      | _ => simp [TermPrim.typeOf] at htyeq
  -- ═══ Integer arithmetic ═══
  | @neg_int _ n _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => -f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @add_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ + fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @sub_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ - fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @mul_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ * fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @div_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ / fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @mod_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ % fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @abs_int _ n _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => if f Γ < 0 then -f Γ else f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  -- ═══ Integer comparisons ═══
  | @le_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≤ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @lt_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ < fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @ge_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≥ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @gt_int _ _ na nb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ > fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms chainable chainable.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  -- ═══ Bitvector arithmetic ═══
  | @bvneg _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => -f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @bvadd _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ + fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; simp,
      by simp [hvala, hvalb]⟩
  | @bvsub _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ - fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvmul _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ * fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvnot _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => ~~~f Γ, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @bvand _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ &&& fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvor _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ||| fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvxor _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ^^^ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvshl _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ <<< fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvlshr _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ >>> fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvashr _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sshiftRight' (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector comparisons ═══
  | @bvslt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.slt (fa Γ) (fb Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsle _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sle (fa Γ) (fb Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvult _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ < fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvule _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≤ fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvsgt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.slt (fb Γ) (fa Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsge _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.sle (fb Γ) (fa Γ) = true,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvugt _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ > fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  | @bvuge _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ≥ fb Γ,
      by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb, decide_eq_true_eq]⟩
  -- ═══ Bitvector division / remainder ═══
  | @bvudiv _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smtUDiv (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvurem _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ % fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @bvsdiv _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smtSDiv (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsrem _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.srem (fa Γ) (fb Γ), by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector overflow predicates ═══
  | @bvnego _ n x _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => BitVec.negOverflow (f Γ) = true, by unfold denoteTerm; rw [hdt]; first | rfl | simp,
      by simp [hval]⟩
  | @bvsaddo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.saddOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvssubo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.ssubOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  | @bvsmulo _ _ n x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => BitVec.smulOverflow (fa Γ) (fb Γ) = true, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩
  -- ═══ Bitvector concatenation and extension ═══
  | @bvconcat _ _ n m x y _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ++ fb Γ, by unfold denoteTerm; rw [hdta, hdtb]; first | rfl | simp, by simp [hvala, hvalb]⟩
  | @zero_extend _ n x _ i _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => BitVec.zeroExtend (n + i) (f Γ), by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  -- ═══ String operations ═══
  | @str_length _ sv _ _ ih =>
    obtain ⟨f, hdt, hval⟩ := ih
    exact ⟨fun Γ => Int.ofNat (f Γ).length, by unfold denoteTerm; rw [hdt]; first | rfl | simp, by simp [hval]⟩
  | @str_concat _ _ sa sb _ _ _ iha ihb =>
    obtain ⟨fa, hdta, hvala⟩ := iha; obtain ⟨fb, hdtb, hvalb⟩ := ihb
    exact ⟨fun Γ => fa Γ ++ fb Γ,
      by unfold denoteTerm denoteTerms denoteTerms denoteTerms leftAssoc leftAssoc.go; rw [hdta, hdtb]; first | rfl | simp,
      by simp [hvala, hvalb]⟩

/-! ### Soundness theorems

These theorems state that `DenotePred t v` implies that the functional
denotation (`denoteBoolTermAux`, `denoteIntTermAux`, `denoteBVTermAux`,
`denoteStringTermAux`) succeeds with a consistent result.  The boolean case
bridges the `Bool`/`Prop` gap: `denoteTerm` maps booleans to `Prop`
(`True`/`False`), while `DenotePred` stays in `Bool`.
-/

/-- Soundness for boolean results: if `DenotePred t (.bool b)` holds, then
    `denoteBoolTermAux` succeeds with a proposition logically equivalent
    to `b = true`. -/
theorem DenotePred.sound_bool {t : Term} {b : Bool}
    (h : DenotePred t (.bool b)) :
    ∃ p, denoteBoolTermAux t = some p ∧ (p ↔ b = true) := by
  obtain ⟨f, hdt, hiff⟩ := DenotePred.sound_aux h
  exact ⟨f tdi₀, by simp [denoteBoolTermAux, hdt], hiff⟩

/-- Soundness for integer results: if `DenotePred t (.int n)` holds, then
    `denoteIntTermAux` succeeds with value `n`. -/
theorem DenotePred.sound_int {t : Term} {n : Int}
    (h : DenotePred t (.int n)) :
    denoteIntTermAux t = some n := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteIntTermAux, hdt, hval]

/-- Soundness for bitvector results: if `DenotePred t (.bitvec x)` holds, then
    `denoteBVTermAux` succeeds with value `x`. -/
theorem DenotePred.sound_bitvec {t : Term} {n : Nat} {x : BitVec n}
    (h : DenotePred t (.bitvec x)) :
    denoteBVTermAux n t = some x := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteBVTermAux, hdt, hval]

/-- Soundness for string results: if `DenotePred t (.string s)` holds, then
    `denoteStringTermAux` succeeds with value `s`. -/
theorem DenotePred.sound_string {t : Term} {s : String}
    (h : DenotePred t (.string s)) :
    denoteStringTermAux t = some s := by
  obtain ⟨f, hdt, hval⟩ := DenotePred.sound_aux h
  simp [denoteStringTermAux, hdt, hval]

/-! ### DenotePred determinism -/

/-- `DenotePred` is deterministic: a term has at most one denotation. -/
theorem DenotePred.deterministic {t : Term} {v₁ v₂ : TermPrim}
    (h₁ : DenotePred t v₁) (h₂ : DenotePred t v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  -- Literals
  | prim_bool | prim_int | prim_bitvec | prim_string => cases h₂; rfl
  -- ITE requires ruling out the opposite branch
  | ite_true _ _ _ _ ihc iha _ =>
    cases h₂ with
    | ite_true _ ha' _ _ => exact iha ha'
    | ite_false hc' _ _ _ => exact absurd (ihc hc') (by simp)
  | ite_false _ _ _ _ ihc _ ihb =>
    cases h₂ with
    | ite_true hc' _ _ _ => exact absurd (ihc hc') (by simp)
    | ite_false _ _ hb' _ => exact ihb hb'
  -- Unary bitvector ops (need `cases` for heterogeneous width equality)
  | bvneg _ ih | bvnot _ ih | bvnego _ ih =>
    cases h₂; have h := ih ‹_›; cases h; rfl
  -- Binary bitvector ops
  | bvadd _ _ iha ihb | bvsub _ _ iha ihb | bvmul _ _ iha ihb
  | bvand _ _ iha ihb | bvor _ _ iha ihb | bvxor _ _ iha ihb
  | bvshl _ _ iha ihb | bvlshr _ _ iha ihb | bvashr _ _ iha ihb
  | bvslt _ _ iha ihb | bvsle _ _ iha ihb | bvult _ _ iha ihb | bvule _ _ iha ihb
  | bvsgt _ _ iha ihb | bvsge _ _ iha ihb | bvugt _ _ iha ihb | bvuge _ _ iha ihb
  | bvudiv _ _ iha ihb | bvurem _ _ iha ihb | bvsdiv _ _ iha ihb | bvsrem _ _ iha ihb
  | bvsaddo _ _ iha ihb | bvssubo _ _ iha ihb | bvsmulo _ _ iha ihb
  | bvconcat _ _ iha ihb =>
    cases h₂; have h1 := iha ‹_›; have h2 := ihb ‹_›; cases h1; cases h2; rfl
  -- zero_extend: unary with extra Nat parameter
  | zero_extend _ _ iha => cases h₂; have := iha ‹_›; cases this; rfl
  -- All remaining (boolean/int/string ops): apply IHs then close with simp_all
  | not _ ih | neg_int _ ih | abs_int _ ih | str_length _ ih =>
    cases h₂; have := ih ‹_›; simp_all
  | _ =>
    rename_i iha ihb; cases h₂; have := iha ‹_›; have := ihb ‹_›; simp_all
