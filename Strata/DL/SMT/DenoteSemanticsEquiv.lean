/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
# Equivalence of `Term.denoteTyped` and `denoteTerm`

This file bridges the two SMT-term denotations Strata carries:

* `Term.denoteTyped` (`Strata.DL.SMT.DenoteTyped`) — the *total*, dependently-typed,
  restricted-fragment semantics. It denotes a term gated on a `Term.typeCheck tyctx tm = .ok τ`
  proof, into `TermType.denoteTyped σ SmtArrayTheory τ` (bool ↦ `Bool`).
* `denoteTerm` (`Strata.DL.SMT.Denote`) — the *partial* (`Option`) semantics, which denotes
  bool ↦ `Prop`, uses positional list environments, and interprets `div`/`mod` with
  Lean's total `/`,`%`.

The headline result (`Term.denoteTyped_denoteTerm_agree`) says: under `EnvCorr`-related environments (the
correspondence between the typed and positional-list environments), on any `Term.typeCheck`-well-typed term
that `denoteTerm` *also* interprets, the two denotations agree up to the per-`TermType` logical relation
`ValEquiv` — built from `PrimValEquiv` at base sorts (whose only non-trivial case is the `Bool`↔`Prop`
bridge `b = true ↔ P`) and extended structurally to the option and array sorts. Because `denoteTerm`
returns `none` for `distinct` nodes, the statement is conditioned on `denoteTerm ctx tm = some res`, so that
construct is covered vacuously. Its companion `Term.denoteTypedArgs_denoteTerms_agree` (proved mutually)
extends the same agreement to argument lists via the pointwise relation `ArgsEquiv`.

Div/mod agree only when `Term.denoteTyped`'s parameters are pinned to Lean's total behavior, so the
theorem fixes `divByZero := fun _ => 0` and `modByZero := id`. Array theory treatments agree only when
`Term.denoteTyped`'s `ArrayTheory` parameter is pinned to `SmtArray`.
-/

module

public import Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTyped
public import Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTypedProps
public import Strata.DL.SMT.Denote
import all Strata.DL.SMT.Denote
public import Strata.DL.SMT.SmtArray
import all Strata.DL.SMT.SmtArray

namespace Strata.SMT.DenoteTyped

variable {σ : SortInterp}

/- ═══════════════════════════════════════════════════════════════════════════
   Sort denotation reductions

   `denoteSort sctx (.prim p)` reduces to the concrete Lean type for any `sctx`.
   These four base-sort reductions are what the agreement proof needs at `.prim` positions.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- `denoteSort` at the `bool` primitive sort evaluates to `Prop`. -/
private theorem dsget_bool (sctx) (h) (sdi) :
    (denoteSort sctx (.prim .bool)).get h sdi = Prop := by
  simp [denoteSort, denotePrimSort]

/-- `denoteSort` at the `int` primitive sort evaluates to `Int`. -/
private theorem dsget_int (sctx) (h) (sdi) :
    (denoteSort sctx (.prim .int)).get h sdi = Int := by
  simp [denoteSort, denotePrimSort]

/-- `denoteSort` at the `string` primitive sort evaluates to `String`. -/
private theorem dsget_str (sctx) (h) (sdi) :
    (denoteSort sctx (.prim .string)).get h sdi = String := by
  simp [denoteSort, denotePrimSort]

/-- `denoteSort` at the `bitvec n` primitive sort evaluates to `BitVec n`. -/
private theorem dsget_bv (sctx) {n : Nat} (h) (sdi) :
    (denoteSort sctx (.prim (.bitvec n))).get h sdi = BitVec n := by
  simp [denoteSort, denotePrimSort]

/- ═══════════════════════════════════════════════════════════════════════════
   The per-`TermType` logical relation
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- The Lean type a `denoteTerm` value inhabits at each denotable base sort. -/
def DenoteTValType : TermType → Type
  | .prim .bool        => Prop
  | .prim .int         => Int
  | .prim .string      => String
  | .prim (.bitvec n)  => BitVec n
  | _                  => PUnit

/-- Logical relation between a `Term.denoteTyped` value and a `denoteTerm` value at each base sort.
    Bool is a bridge (`b = true ↔ P`); the other denotable base sorts are equality. -/
def PrimValEquiv : (τ : TermType) → TermType.denoteTyped σ SmtArrayTheory τ → DenoteTValType τ → Prop
  | .prim .bool,       b, P =>
    -- This `Bool`↔`Prop` bridge is the semantic justification for the correctness of Strata-Boole's
    -- verification-condition generation, where the verification conditions are denoted to `Prop`.
    -- (See the Strata-Boole repository: https://github.com/strata-org/Strata-Boole)
    (b = true ↔ P)
  | .prim .int,        i, j => i = j
  | .prim .string,     s, t => s = t
  | .prim (.bitvec _), x, y => x = y
  | .prim .real,       _, _ => False
  | .prim .regex,      _, _ => False
  | .option _,         _, _ => False
  | .constr _ _,       _, _ => False

/-- Transport a primitive `denoteTerm` value (living in `(denoteSort sctx τ).get h sdi`) into the concrete
    `DenoteTValType τ`, so it can be fed to `PrimValEquiv`. Base sorts use the `dsget_*` reductions;
    all other sorts are unreachable (`.real`/`.regex` are not denotable; `.option`/`.constr`
    are handled by `ValEquiv` directly), so their values are irrelevant. -/
def toTVal : (sctx : SortContext) → (τ : TermType) → (h : (denoteSort sctx τ).isSome) →
    (sdi : SortDenoteInput sctx) → (denoteSort sctx τ).get h sdi → DenoteTValType τ
  | sctx, .prim .bool,       h, sdi, x => cast (dsget_bool sctx h sdi) x
  | sctx, .prim .int,        h, sdi, x => cast (dsget_int sctx h sdi) x
  | sctx, .prim .string,     h, sdi, x => cast (dsget_str sctx h sdi) x
  | sctx, .prim (.bitvec _), h, sdi, x => cast (dsget_bv sctx h sdi) x
  | _,    .prim .real,       _, _,   _ => ⟨⟩
  | _,    .prim .regex,      _, _,   _ => ⟨⟩
  | _,    .option _,         _, _,   _ => ⟨⟩
  | _,    .constr _ _,       _, _,   _ => ⟨⟩

/-- The relation between a `Term.denoteTyped` value at sort `τ` and a raw `denoteTerm` value at the
    same sort. At denotable base sorts it is `PrimValEquiv` on the value transported through `toTVal`.
    At an uninterpreted sort (`.constr`) the SMT carrier is `σ id args` and the `denoteTerm`
    carrier is the model's realization; we relate them by heterogeneous equality `HEq`. -/
def ValEquiv (sctx : SortContext) : (τ : TermType) → (smt : TermType.denoteTyped σ SmtArrayTheory τ) →
    (h : (denoteSort sctx τ).isSome) → (sdi : SortDenoteInput sctx) →
    (g : (denoteSort sctx τ).get h sdi) → Prop
  | .constr "Array" [k, v], smt, h, sdi, g =>
      -- Arrays are related extensionally: related keys map to related values. A plain `HEq` fails
      -- because the element sorts can differ (`bool` ↦ `Bool` vs `Prop`).
      ∀ (ka : TermType.denoteTyped σ SmtArrayTheory k)
        (kb : (denoteSort sctx k).get (denoteSortArray_isSome_key h) sdi),
        ValEquiv sctx k ka (denoteSortArray_isSome_key h) sdi kb →
        ValEquiv sctx v (smt.select ka) (denoteSortArray_isSome_val h) sdi
          ((cast denoteSortArray_Some g).select kb)
  | .constr _ _, smt, _,   _,   g => HEq smt g
  | .option ty,  smt, h,   sdi, g =>
      -- both `smt` and `g` are `Option`s (faithful `TermType.denoteTyped`/`denoteSort`); relate structurally,
      -- recursing on the inner value (a plain `HEq` fails due to the `Bool`/`Prop` mismatch).
      match smt, cast denoteSortOption_Some g with
      | none,   none   => True
      | some a, some b => ValEquiv sctx ty a (denoteSortOption_isSome h) sdi b
      | _,      _      => False
  | .prim p,     smt, h,   sdi, g => PrimValEquiv (.prim p) smt (toTVal sctx (.prim p) h sdi g)

/- ═══════════════════════════════════════════════════════════════════════════
   Environment correspondence

   Keyed on the denoteTerm-side environment entries: for every variable / UF the `denoteTerm`
   environment knows about, the `VarEnv` / `UFInterp` agrees on it (up to `ValEquiv`). Because
   `denoteTerm` only ever reads entries it locates, and reads that miss make `denoteTerm` return
   `none`, this correspondence is exactly what the equivalence needs.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Pointwise `ValEquiv` between an `HList` of SMT argument values and a list of `denoteTerm` argument
    results (each evaluated at `tdi`). Used to feed related arguments to a UF interpretation. -/
def ArgsEquiv {ctx : Context} (tdi : TermDenoteInput ctx) :
    (argTys : List TermType) → HList (TermType.denoteTyped σ SmtArrayTheory) argTys → List (TermDenoteResult ctx) → Prop
  | [],         .nil,       []      => True
  | ty :: tys,  .cons x xs, r :: rs =>
      (∃ (heq : ty = r.ty), ValEquiv ctx.sctx r.ty (heq ▸ x) r.h ⟨tdi.sΓ, tdi.hsΓ⟩ (r.res tdi))
        ∧ ArgsEquiv tdi tys xs rs
  | _,          _,          _       => False

/-- A denoted argument VALUE: a `denoteTerm` result already evaluated at a fixed sort-denotation input.
    Value-level analog of `TermDenoteResult`, depending only on `sctx`/`sdi` — NOT on the variable
    context. This is what makes `EnvCorr.huf` context-independent, so that extending the environment
    with a new quantifier binder preserves it definitionally. -/
structure TermValDenote {sctx : SortContext} (sdi : SortDenoteInput sctx) where
  ty : TermType
  h : (denoteSort sctx ty).isSome
  val : (denoteSort sctx ty).get h sdi

def valTypesAlign {sctx : SortContext} {sdi : SortDenoteInput sctx}
    (vs : List (TermValDenote sdi)) (tys : List TermType) : Bool :=
  match vs, tys with
  | [], []             => true
  | v :: vs, ty :: tys => v.ty == ty && valTypesAlign vs tys
  | _, _               => false

/-- Apply a UF's semantic function to a list of denoted argument VALUES. Value-level analog of
    `applyUFAux` (threads `v.val` where `applyUFAux` threads `a.res tdi`). -/
noncomputable def applyUFValAux {sctx : SortContext} {sdi : SortDenoteInput sctx} :
    (args : List TermType) → (out : TermType) → (h : (denoteFunSort sctx args out).isSome) →
    (denoteFunSort sctx args out).get h sdi → (vs : List (TermValDenote sdi)) →
    (hl : args.length = vs.length) →
    (∀ i, (hi : i < vs.length) → (vs[i]'hi).ty = (args[i]'(hl ▸ hi))) →
    (denoteSort sctx out).get (denoteSortOut_isSome_of_denoteFunSort_isSome h) sdi
  | [], _, _, uf, [], _, _ => uf
  | arg :: _, _, h, uf, v :: vs, hl, has =>
    let uf := arrow_of_denoteFunSortCons_isSome h ▸ uf
    have ha : denoteSort sctx arg = denoteSort sctx v.ty := has 0 (Nat.zero_lt_succ _) ▸ rfl
    applyUFValAux _ _ (denoteFunSortCons_isSome h).right (uf (Option.get_congr ha ▸ v.val)) vs
      (Nat.succ.inj hl) (fun i hi => has (i + 1) (Nat.succ_lt_succ hi))

/-- A `valTypesAlign`-aligned value list has the same length as the type list it aligns with. -/
private theorem valTypesAlign_length_eq {sctx : SortContext} {sdi : SortDenoteInput sctx}
    {vs : List (TermValDenote sdi)} {tys : List TermType} (h : valTypesAlign vs tys) :
    vs.length = tys.length := by
  induction vs generalizing tys with
  | nil => cases tys with
    | nil => rfl
    | cons => simp [valTypesAlign] at h
  | cons v vs ih => cases tys with
    | nil => simp [valTypesAlign] at h
    | cons ty tys =>
      simp only [valTypesAlign, Bool.and_eq_true] at h
      simp [List.length_cons, ih h.2]

/-- Each element of a `valTypesAlign`-aligned value list has the same `TermType` as the
    corresponding entry in the type list. -/
private theorem valTypesAlign_arg_types {sctx : SortContext} {sdi : SortDenoteInput sctx}
    {vs : List (TermValDenote sdi)} {tys : List TermType} (h : valTypesAlign vs tys) :
    ∀ i, (hi : i < vs.length) → (vs[i]'hi).ty = (tys[i]'(valTypesAlign_length_eq h ▸ hi)) := by
  induction vs generalizing tys with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons v vs ih => cases tys with
    | nil => simp [valTypesAlign] at h
    | cons ty tys =>
      simp only [valTypesAlign, Bool.and_eq_true, beq_iff_eq] at h
      intro i hi
      match i with
      | 0 => exact h.1
      | j + 1 => exact ih h.2 j (by simpa using hi)

/-- Apply a UF's semantic function to a `valTypesAlign`-aligned value list. -/
noncomputable def applyUFVal {sctx : SortContext} {sdi : SortDenoteInput sctx}
    (args : List TermType) (out : TermType) (h : (denoteFunSort sctx args out).isSome)
    (uf : (denoteFunSort sctx args out).get h sdi) (vs : List (TermValDenote sdi))
    (hAlign : valTypesAlign vs args) :
    (denoteSort sctx out).get (denoteSortOut_isSome_of_denoteFunSort_isSome h) sdi :=
  applyUFValAux args out h uf vs (valTypesAlign_length_eq hAlign).symm (valTypesAlign_arg_types hAlign)

/-- Value-level `ArgsEquiv`: pointwise `ValEquiv` between an `HList` of SMT values and a list of denoted
    argument VALUES. -/
def ArgsValEquiv {sctx : SortContext} (sdi : SortDenoteInput sctx) :
    (argTys : List TermType) → HList (TermType.denoteTyped σ SmtArrayTheory) argTys → List (TermValDenote sdi) → Prop
  | [],         .nil,       []      => True
  | ty :: tys,  .cons x xs, v :: vs =>
      (∃ (heq : ty = v.ty), ValEquiv sctx v.ty (heq ▸ x) v.h sdi v.val) ∧ ArgsValEquiv sdi tys xs vs
  | _,          _,          _       => False

/-- Correspondence between the typed denotation environments and a `denoteTerm` input `tdi`. -/
structure EnvCorr {ctx : Context} (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory)
    (tdi : TermDenoteInput ctx) : Prop where
  /-- The environments agree on every variable entry that is not shadowed. -/
  hvar : ∀ (i : Nat) (hi : i < tdi.tΓ.vs.length),
    ctx.tctx.vs.findIdx? (· == (tdi.tΓ.vs[i]'hi).var) = some i →
    ValEquiv ctx.sctx (tdi.tΓ.vs[i]'hi).var.ty (env (tdi.tΓ.vs[i]'hi).var)
      (tdi.tΓ.vs[i]'hi).h ⟨tdi.sΓ, tdi.hsΓ⟩ (tdi.tΓ.vs[i]'hi).varΓ
  /-- For every UF entry, the SMT interpretation agrees with the stored semantic function, pointwise over
      related argument VALUES. -/
  huf : ∀ (i : Nat) (hi : i < tdi.tΓ.ufs.length)
          (hargs : HList (TermType.denoteTyped σ SmtArrayTheory) (tdi.tΓ.ufs[i]'hi).uf.args)
          (gvals : List (TermValDenote (⟨tdi.sΓ, tdi.hsΓ⟩ : SortDenoteInput ctx.sctx)))
          (hAlign : valTypesAlign gvals (tdi.tΓ.ufs[i]'hi).uf.args),
          ArgsValEquiv ⟨tdi.sΓ, tdi.hsΓ⟩ (tdi.tΓ.ufs[i]'hi).uf.args hargs gvals →
          ValEquiv ctx.sctx (tdi.tΓ.ufs[i]'hi).uf.out
            (UF.applyDenoteTyped' σ SmtArrayTheory (tdi.tΓ.ufs[i]'hi).uf.args (tdi.tΓ.ufs[i]'hi).uf.out
              (ufInterp (tdi.tΓ.ufs[i]'hi).uf) hargs)
            (denoteSortOut_isSome_of_denoteFunSort_isSome (tdi.tΓ.ufs[i]'hi).h)
            ⟨tdi.sΓ, tdi.hsΓ⟩
            (applyUFVal (tdi.tΓ.ufs[i]'hi).uf.args (tdi.tΓ.ufs[i]'hi).uf.out
              (tdi.tΓ.ufs[i]'hi).h (tdi.tΓ.ufs[i]'hi).ufΓ gvals hAlign)
  /-- At every denotable `.constr id args` sort, the sort denotations agree. -/
  hsort : ∀ (id : String) (args : List TermType)
            (h : (denoteSort ctx.sctx (.constr id args)).isSome),
            TermType.denoteTyped σ SmtArrayTheory (.constr id args)
              = (denoteSort ctx.sctx (.constr id args)).get h ⟨tdi.sΓ, tdi.hsΓ⟩

/-- Build `ValEquiv` at `bool` from an iff, given the raw denote value is `HEq` to a genuine `Prop`. -/
private theorem ValEquiv_bool_mk {σ : SortInterp} {sctx : SortContext} {b : TermType.denoteTyped σ SmtArrayTheory (.prim .bool)} {h sdi} {g} {P : Prop}
    (hgP : HEq g P) (hiff : (b = true) ↔ P) : ValEquiv sctx (.prim .bool) b h sdi g := by
  have he : toTVal sctx (.prim .bool) h sdi g = P :=
    eq_of_heq (HEq.trans (show HEq (toTVal sctx (.prim .bool) h sdi g) g by
      simp only [toTVal]; exact cast_heq _ _) hgP)
  show (b = true) ↔ toTVal sctx (.prim .bool) h sdi g
  rw [he]; exact hiff

/-- Extract the iff from `ValEquiv` at `bool`, given the raw denote value is `HEq` to a genuine `Prop`. -/
private theorem ValEquiv_bool_elim {σ : SortInterp} {sctx : SortContext} {b : TermType.denoteTyped σ SmtArrayTheory (.prim .bool)} {h sdi} {g} {P : Prop}
    (hgP : HEq g P) (hrel : ValEquiv sctx (.prim .bool) b h sdi g) : (b = true) ↔ P := by
  have he : toTVal sctx (.prim .bool) h sdi g = P :=
    eq_of_heq (HEq.trans (show HEq (toTVal sctx (.prim .bool) h sdi g) g by
      simp only [toTVal]; exact cast_heq _ _) hgP)
  have h2 : (b = true) ↔ toTVal sctx (.prim .bool) h sdi g := hrel
  rw [he] at h2; exact h2

/-- Bridge lemma: at a non-`Array` uninterpreted sort `.constr id args`, `ValEquiv` reduces to the plain
    heterogeneous equality `HEq smt g`. -/
private theorem ValEquiv_constr_heq {sctx : SortContext} {id : String} {args : List TermType}
    (hne : ∀ k v, id = "Array" → args = [k, v] → False)
    {smt : TermType.denoteTyped σ SmtArrayTheory (.constr id args)}
    {h : (denoteSort sctx (.constr id args)).isSome} {sdi : SortDenoteInput sctx}
    {g : (denoteSort sctx (.constr id args)).get h sdi} :
    ValEquiv sctx (.constr id args) smt h sdi g = HEq smt g := by
  rw [ValEquiv]
  intro k v _ _ _ _ _ hid harg _
  exact hne k v hid harg

mutual
/-- **`ValEquiv` respects equality**: if `a`/`b` relate to `x`/`y` at the same sort, then `a = b ↔ x = y`. -/
private theorem ValEquiv_eq_iff {sctx : SortContext} {τ : TermType}
    {a b : TermType.denoteTyped σ SmtArrayTheory τ} {h : (denoteSort sctx τ).isSome} {sdi : SortDenoteInput sctx}
    {x y : (denoteSort sctx τ).get h sdi}
    (hsort : ∀ (id : String) (args : List TermType) (hc : (denoteSort sctx (.constr id args)).isSome),
        TermType.denoteTyped σ SmtArrayTheory (.constr id args) = (denoteSort sctx (.constr id args)).get hc sdi)
    (ha : ValEquiv sctx τ a h sdi x) (hb : ValEquiv sctx τ b h sdi y) : (a = b) ↔ (x = y) := by
  cases τ with
  | option ty =>
    unfold ValEquiv at ha hb
    -- `x = y ↔ (cast x) = (cast y)` (cast along `denoteSortOption_Some` is injective), then case both
    -- `Option`s; the `some/some` case recurses via `ValEquiv_eq_iff` at `ty`.
    have hinj : (x = y) ↔ (cast denoteSortOption_Some x = cast denoteSortOption_Some y) := by
      refine ⟨fun e => by rw [e], fun e => ?_⟩
      have h2 := congrArg
        (cast (denoteSortOption_Some (sctx := sctx) (ty := ty) (h := h) (sΓ := sdi)).symm) e
      rwa [cast_cast, cast_eq, cast_cast, cast_eq] at h2
    rw [hinj]
    cases a <;> cases b <;> cases hcx : cast denoteSortOption_Some x <;>
      cases hcy : cast denoteSortOption_Some y <;>
      simp_all only [reduceCtorEq, Option.some.injEq, iff_self, iff_false] <;>
      first
      | rfl
      | exact ValEquiv_eq_iff hsort ha hb
  | constr id args =>
    by_cases hArr : ∃ k v, id = "Array" ∧ args = [k, v]
    · obtain ⟨k, v, hid, hargs⟩ := hArr
      subst hid; subst hargs
      -- Array extensional equality: `a = b ↔ x = y` where both are arrays. Two arrays are equal iff
      -- they agree at every index; the `ValEquiv`-recursion at `k`/`v` bridges keys and values, and
      -- `ValEquiv_cover` at `k` supplies a related key for each denote/SMT key.
      simp only [ValEquiv] at ha hb
      obtain ⟨covk1, covk2⟩ := ValEquiv_cover k (denoteSortArray_isSome_key h) sdi hsort
      constructor
      · intro hab
        -- `x = y`: agree at every denote key `kb`; pick an SMT key related to `kb`.
        have hcast : (cast denoteSortArray_Some x : SmtArray _ _)
            = (cast denoteSortArray_Some y : SmtArray _ _) := by
          apply SmtArray.ext
          intro kb
          have hka : ValEquiv sctx k (Classical.choose (covk2 kb)) (denoteSortArray_isSome_key h) sdi kb :=
            Classical.choose_spec (covk2 kb)
          exact (ValEquiv_eq_iff hsort (ha (Classical.choose (covk2 kb)) kb hka)
            (hb (Classical.choose (covk2 kb)) kb hka)).mp (by rw [hab])
        have h2 := congrArg
          (cast (denoteSortArray_Some (sctx := sctx) (kTy := k) (vTy := v) (h := h) (sΓ := sdi)).symm)
          hcast
        rwa [cast_cast, cast_eq, cast_cast, cast_eq] at h2
      · intro hxy
        -- `a = b`: agree at every SMT key `ka`; pick a denote key related to `ka`.
        apply SmtArray.ext
        intro ka
        have hkb : ValEquiv sctx k ka (denoteSortArray_isSome_key h) sdi (Classical.choose (covk1 ka)) :=
          Classical.choose_spec (covk1 ka)
        exact (ValEquiv_eq_iff hsort (ha ka (Classical.choose (covk1 ka)) hkb)
          (hb ka (Classical.choose (covk1 ka)) hkb)).mpr (by rw [hxy])
    · rw [ValEquiv_constr_heq (fun k v hid hargs => hArr ⟨k, v, hid, hargs⟩)] at ha hb
      exact ⟨fun hab => eq_of_heq (ha.symm.trans ((heq_of_eq hab).trans hb)),
             fun hxy => eq_of_heq (ha.trans ((heq_of_eq hxy).trans hb.symm))⟩
  | prim p =>
    unfold ValEquiv at ha hb
    cases p with
    | bool =>
      simp only [PrimValEquiv] at ha hb
      rw [show toTVal sctx (.prim .bool) h sdi x = x from
            eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at ha
      rw [show toTVal sctx (.prim .bool) h sdi y = y from
            eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hb
      refine ⟨fun hab => ?_, fun hxy => ?_⟩
      · subst hab; exact propext (ha.symm.trans hb)
      · have hiff : (a = true) ↔ (b = true) := ha.trans (hxy.symm ▸ hb.symm)
        clear ha hb hxy
        cases a <;> cases b <;> simp_all
    | int =>
      simp only [PrimValEquiv] at ha hb
      have hax : a = x := ha.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      have hby : b = y := hb.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      exact ⟨fun hab => by rw [← hax, ← hby]; exact hab, fun hxy => by rw [hax, hby]; exact hxy⟩
    | string =>
      simp only [PrimValEquiv] at ha hb
      have hax : a = x := ha.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      have hby : b = y := hb.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      exact ⟨fun hab => by rw [← hax, ← hby]; exact hab, fun hxy => by rw [hax, hby]; exact hxy⟩
    | bitvec n =>
      simp only [PrimValEquiv] at ha hb
      have hax : a = x := ha.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      have hby : b = y := hb.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))
      exact ⟨fun hab => by rw [← hax, ← hby]; exact hab, fun hxy => by rw [hax, hby]; exact hxy⟩
    | real => simp [denoteSort, denotePrimSort] at h
    | regex => simp [denoteSort, denotePrimSort] at h

/-- **`ValEquiv` is total from both sides** at every denotable sort: every SMT value has a `ValEquiv`-related
    realization and vice versa. -/
private theorem ValEquiv_cover {sctx : SortContext} (ty : TermType)
    (h : (denoteSort sctx ty).isSome) (sdi : SortDenoteInput sctx)
    (hsort : ∀ (id : String) (args : List TermType) (hc : (denoteSort sctx (.constr id args)).isSome),
        TermType.denoteTyped σ SmtArrayTheory (.constr id args) = (denoteSort sctx (.constr id args)).get hc sdi) :
    (∀ a : TermType.denoteTyped σ SmtArrayTheory ty, ∃ x, ValEquiv sctx ty a h sdi x) ∧
    (∀ x, ∃ a : TermType.denoteTyped σ SmtArrayTheory ty, ValEquiv sctx ty a h sdi x) := by
  cases ty with
  | prim p =>
    cases p with
    | bool =>
      constructor
      · intro a
        refine ⟨cast (dsget_bool sctx h sdi).symm (a = true), ?_⟩
        have heq : toTVal sctx (.prim .bool) h sdi (cast (dsget_bool sctx h sdi).symm (a = true))
            = (a = true) := by simp only [toTVal]; exact eq_of_heq (cast_heq _ _)
        show (a = true) ↔ toTVal sctx (.prim .bool) h sdi (cast (dsget_bool sctx h sdi).symm (a = true))
        exact heq ▸ Iff.rfl
      · intro x
        refine ⟨@decide (toTVal sctx (.prim .bool) h sdi x) (Classical.propDecidable _), ?_⟩
        show (@decide (toTVal sctx (.prim .bool) h sdi x) (Classical.propDecidable _) = true)
              ↔ toTVal sctx (.prim .bool) h sdi x
        exact @decide_eq_true_iff (toTVal sctx (.prim .bool) h sdi x) (Classical.propDecidable _)
    | int =>
      constructor
      · intro a
        refine ⟨cast (dsget_int sctx h sdi).symm a, ?_⟩
        show a = toTVal sctx (.prim .int) h sdi (cast (dsget_int sctx h sdi).symm a)
        simp only [toTVal]; exact eq_of_heq (cast_heq _ _).symm
      · intro x
        exact ⟨toTVal sctx (.prim .int) h sdi x, rfl⟩
    | string =>
      constructor
      · intro a
        refine ⟨cast (dsget_str sctx h sdi).symm a, ?_⟩
        show a = toTVal sctx (.prim .string) h sdi (cast (dsget_str sctx h sdi).symm a)
        simp only [toTVal]; exact eq_of_heq (cast_heq _ _).symm
      · intro x
        exact ⟨toTVal sctx (.prim .string) h sdi x, rfl⟩
    | bitvec n =>
      constructor
      · intro a
        refine ⟨cast (dsget_bv sctx h sdi).symm a, ?_⟩
        show a = toTVal sctx (.prim (.bitvec n)) h sdi (cast (dsget_bv sctx h sdi).symm a)
        simp only [toTVal]; exact eq_of_heq (cast_heq _ _).symm
      · intro x
        exact ⟨toTVal sctx (.prim (.bitvec n)) h sdi x, rfl⟩
    | real =>
      simp only [denoteSort, denotePrimSort, Option.isSome] at h; exact absurd h Bool.false_ne_true
    | regex =>
      simp only [denoteSort, denotePrimSort, Option.isSome] at h; exact absurd h Bool.false_ne_true
  | option ty' =>
    -- Both sides are `Option`s now; recurse on the inner sort for the `some` case.
    have hty' : (denoteSort sctx ty').isSome := denoteSortOption_isSome h
    obtain ⟨cov1, cov2⟩ := ValEquiv_cover ty' hty' sdi hsort
    refine ⟨fun a => ?_, fun x => ?_⟩
    · match a with
      | none =>
        refine ⟨cast denoteSortOption_Some.symm none, ?_⟩
        show ValEquiv sctx (.option ty') none h sdi (cast denoteSortOption_Some.symm none)
        simp only [ValEquiv, cast_cast, cast_eq]
      | some a' =>
        obtain ⟨b', hb'⟩ := cov1 a'
        refine ⟨cast denoteSortOption_Some.symm (some b'), ?_⟩
        show ValEquiv sctx (.option ty') (some a') h sdi (cast denoteSortOption_Some.symm (some b'))
        simp only [ValEquiv, cast_cast, cast_eq]
        exact hb'
    · match hxc : (cast denoteSortOption_Some x : Option _) with
      | none =>
        refine ⟨none, ?_⟩
        show ValEquiv sctx (.option ty') none h sdi x
        simp only [ValEquiv, hxc]
      | some b =>
        obtain ⟨a', ha'⟩ := cov2 b
        refine ⟨some a', ?_⟩
        show ValEquiv sctx (.option ty') (some a') h sdi x
        simp only [ValEquiv]; rw [hxc]; exact ha'
  | constr id args =>
    by_cases hArr : ∃ k v, id = "Array" ∧ args = [k, v]
    · obtain ⟨k, v, hid, hargs⟩ := hArr
      subst hid; subst hargs
      obtain ⟨covk1, covk2⟩ := ValEquiv_cover k (denoteSortArray_isSome_key h) sdi hsort
      obtain ⟨covv1, covv2⟩ := ValEquiv_cover v (denoteSortArray_isSome_val h) sdi hsort
      constructor
      · -- Every SMT array `a` has a `ValEquiv`-related denote array, built pointwise over denote keys.
        intro a
        refine ⟨cast denoteSortArray_Some.symm
            ⟨fun kb => Classical.choose (covv1 (a.select (Classical.choose (covk2 kb))))⟩, ?_⟩
        simp only [ValEquiv, cast_cast, cast_eq]
        intro ka kb hkab
        have hka' : ValEquiv sctx k (Classical.choose (covk2 kb)) (denoteSortArray_isSome_key h) sdi kb :=
          Classical.choose_spec (covk2 kb)
        have hkeq : ka = Classical.choose (covk2 kb) := (ValEquiv_eq_iff hsort hkab hka').mpr rfl
        show ValEquiv sctx v (a.select ka) (denoteSortArray_isSome_val h) sdi
          (Classical.choose (covv1 (a.select (Classical.choose (covk2 kb)))))
        rw [hkeq]
        exact Classical.choose_spec (covv1 (a.select (Classical.choose (covk2 kb))))
      · -- Every denote array `x` has a `ValEquiv`-related SMT array, built pointwise over SMT keys.
        intro x
        refine ⟨⟨fun ka => Classical.choose
            (covv2 ((cast denoteSortArray_Some x).select (Classical.choose (covk1 ka))))⟩, ?_⟩
        simp only [ValEquiv]
        intro ka kb hkab
        have hkb' : ValEquiv sctx k ka (denoteSortArray_isSome_key h) sdi (Classical.choose (covk1 ka)) :=
          Classical.choose_spec (covk1 ka)
        have hkeq : kb = Classical.choose (covk1 ka) := (ValEquiv_eq_iff hsort hkab hkb').mp rfl
        show ValEquiv sctx v (Classical.choose
            (covv2 ((cast denoteSortArray_Some x).select (Classical.choose (covk1 ka)))))
          (denoteSortArray_isSome_val h) sdi ((cast denoteSortArray_Some x).select kb)
        rw [hkeq]
        exact Classical.choose_spec
          (covv2 ((cast denoteSortArray_Some x).select (Classical.choose (covk1 ka))))
    · have hne : ∀ k v, id = "Array" → args = [k, v] → False :=
        fun k v hid hargs => hArr ⟨k, v, hid, hargs⟩
      constructor
      · intro a
        refine ⟨cast (hsort id args h) a, ?_⟩
        rw [ValEquiv_constr_heq hne]; exact (cast_heq _ _).symm
      · intro x
        refine ⟨cast (hsort id args h).symm x, ?_⟩
        rw [ValEquiv_constr_heq hne]; exact cast_heq _ _
end

/-- Extract the underlying equality from `ValEquiv` at `int`. -/
private theorem ValEquiv_int_get {σ : SortInterp} {sctx : SortContext} {a : TermType.denoteTyped σ SmtArrayTheory (.prim .int)}
    {h sdi} {g : (denoteSort sctx (.prim .int)).get h sdi} (hrel : ValEquiv sctx (.prim .int) a h sdi g) :
    a = g := by
  have h' : PrimValEquiv (.prim .int) a (toTVal sctx (.prim .int) h sdi g) := hrel
  simp only [PrimValEquiv] at h'
  exact h'.trans (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _))

/-- Build `ValEquiv` at `int` from the underlying equality. -/
private theorem ValEquiv_int_mk {σ : SortInterp} {sctx : SortContext} {a : TermType.denoteTyped σ SmtArrayTheory (.prim .int)}
    {h sdi} {g : (denoteSort sctx (.prim .int)).get h sdi} (hag : a = g) :
    ValEquiv sctx (.prim .int) a h sdi g := by
  show PrimValEquiv (.prim .int) a (toTVal sctx (.prim .int) h sdi g)
  simp only [PrimValEquiv]
  rw [hag]; exact (eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)).symm

/-- Single-context congruence: applying a UF to `denoteTerm` results at `tdi` equals applying it to the
    corresponding VALUES (each result evaluated at `tdi`). This is the (easy, same-context) bridge that
    lets the `uf` case feed the value-level `EnvCorr.huf`. -/
private theorem applyUFAux_eq_applyUFValAux {ctx : Context} (tdi : TermDenoteInput ctx) :
    (args : List TermType) → (out : TermType) → (h : (denoteFunSort ctx.sctx args out).isSome) →
    (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩) →
    (as : List (TermDenoteResult ctx)) → (hl : args.length = as.length) →
    (has : ∀ i, (hi : i < as.length) → (as[i]'hi).ty = (args[i]'(hl ▸ hi))) →
    applyUFAux tdi uf as hl has
      = applyUFValAux args out h uf (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩))
          (by rw [List.length_map]; exact hl)
          (fun i hi => by rw [List.getElem_map]; exact has i (by rw [List.length_map] at hi; exact hi))
  | [], _, _, uf, [], _, _ => by simp only [applyUFAux, applyUFValAux, List.map_nil]
  | arg :: args, out, h, uf, a :: as, hl, has => by
      simp only [applyUFAux, applyUFValAux, List.map_cons]
      exact applyUFAux_eq_applyUFValAux tdi args out (denoteFunSortCons_isSome h).right _ as
        (Nat.succ.inj hl) (fun i hi => has (i + 1) (Nat.succ_lt_succ hi))

/-- Applying a UF's semantic function via `applyUF` to the `denoteTerm` results at `tdi` equals applying
    it via `applyUFVal` to the corresponding list of evaluated argument values. -/
private theorem applyUF_eq_applyUFVal {ctx : Context} (tdi : TermDenoteInput ctx)
    (args : List TermType) (out : TermType) (h : (denoteFunSort ctx.sctx args out).isSome)
    (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (as : List (TermDenoteResult ctx)) (hAlign : argTypesAlign as args)
    (hAlignV : valTypesAlign (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩)) args) :
    applyUF tdi uf as hAlign
      = applyUFVal args out h uf (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩)) hAlignV := by
  rw [applyUF, applyUFVal, applyUFAux_eq_applyUFValAux]

/-- `argTypesAlign` transfers to `valTypesAlign` on the evaluated value list. -/
private theorem argTypesAlign_to_valTypesAlign {ctx : Context} (tdi : TermDenoteInput ctx)
    (as : List (TermDenoteResult ctx)) (args : List TermType) (hAlign : argTypesAlign as args) :
    valTypesAlign (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩)) args := by
  induction as generalizing args with
  | nil => cases args with
    | nil => rfl
    | cons => simp [argTypesAlign] at hAlign
  | cons a as ih => cases args with
    | nil => simp [argTypesAlign] at hAlign
    | cons ty tys =>
      simp only [argTypesAlign, Bool.and_eq_true] at hAlign
      simp only [List.map_cons, valTypesAlign, Bool.and_eq_true]
      exact ⟨hAlign.1, ih tys hAlign.2⟩

/-- `ArgsEquiv` transfers to `ArgsValEquiv` on the evaluated value list. -/
private theorem argsRel_to_argsValEquiv {ctx : Context} (tdi : TermDenoteInput ctx)
    (argTys : List TermType) (hargs : HList (TermType.denoteTyped σ SmtArrayTheory) argTys)
    (gargs : List (TermDenoteResult ctx)) (hr : ArgsEquiv tdi argTys hargs gargs) :
    ArgsValEquiv ⟨tdi.sΓ, tdi.hsΓ⟩ argTys hargs (gargs.map (fun a => ⟨a.ty, a.h, a.res tdi⟩)) := by
  induction argTys generalizing gargs with
  | nil => cases hargs; cases gargs with
    | nil => exact True.intro
    | cons => exact hr.elim
  | cons ty tys ih =>
    match hargs, gargs with
    | .cons x xs, r :: rs =>
      obtain ⟨⟨heq, hrel⟩, hrest⟩ := hr
      exact ⟨⟨heq, hrel⟩, ih xs rs hrest⟩
    | .cons _ _, [] => exact hr.elim

/-- When the uninterpreted function recorded in the environment (`uf'`) is provably equal to the one
    written in the term (`uf`), the typed denotation computed for `uf'` can be transferred to `uf`
    while preserving its value-relation (`ValEquiv`) with the partial semantics — i.e. applying either
    UF to related arguments yields related results. -/
private theorem uf_ValEquiv_transport {σ : SortInterp} {ctx : Context} {tdi : TermDenoteInput ctx}
    (ufInterp : UFInterp σ SmtArrayTheory) (uf uf' : UF) (hufeq : uf' = uf)
    (sargs : HList (TermType.denoteTyped σ SmtArrayTheory) uf.args) (as : List (TermDenoteResult ctx))
    (hf : (denoteFunSort ctx.sctx uf.args uf.out).isSome)
    (hf' : (denoteFunSort ctx.sctx uf'.args uf'.out).isSome)
    (eufΓ : (denoteFunSort ctx.sctx uf'.args uf'.out).get hf' ⟨tdi.sΓ, tdi.hsΓ⟩)
    (hufas : argTypesAlign as uf.args)
    (hufΓ : denoteFunSort ctx.sctx uf.args uf.out = denoteFunSort ctx.sctx uf'.args uf'.out)
    (key : ValEquiv ctx.sctx uf'.out
            (UF.applyDenoteTyped' σ SmtArrayTheory uf'.args uf'.out (ufInterp uf') (hufeq.symm ▸ sargs))
            (denoteSortOut_isSome_of_denoteFunSort_isSome hf') ⟨tdi.sΓ, tdi.hsΓ⟩
            (applyUFVal uf'.args uf'.out hf' eufΓ (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩))
              (hufeq.symm ▸ argTypesAlign_to_valTypesAlign tdi as uf.args hufas))) :
    ValEquiv ctx.sctx uf.out
      (UF.applyDenoteTyped' σ SmtArrayTheory uf.args uf.out (ufInterp uf) sargs)
      (denoteSortOut_isSome_of_denoteFunSort_isSome hf) ⟨tdi.sΓ, tdi.hsΓ⟩
      (@applyUF ctx uf.args uf.out hf tdi (Option.get_congr hufΓ ▸ eufΓ) as hufas) := by
  subst uf'
  rw [applyUF_eq_applyUFVal tdi uf.args uf.out hf eufΓ as hufas
        (argTypesAlign_to_valTypesAlign tdi as uf.args hufas)]
  exact key

/-- Convert an `Eq.rec` transport along the `TermType.denoteTyped σ SmtArrayTheory` motive into a `cast`. -/
private theorem denoteTyped_eqRec_eq_cast {σ : SortInterp} {a b : TermType} (h : a = b)
    (x : TermType.denoteTyped σ SmtArrayTheory a) :
    h ▸ x = cast (congrArg (TermType.denoteTyped σ SmtArrayTheory) h) x := by
  cases h; rfl

/-- A `cast` cancels the inverse `Eq.rec` transport it wraps. -/
private theorem cast_eqRec_self {α β : Sort u} (h : α = β) (x : β) : cast h (h ▸ x) = x := by
  cases h; rfl

/-- Unfolding lemma for `denoteTerms` on a cons. -/
private theorem denoteTerms_cons (ctx : Context) (t : Term) (ts : List Term) :
    denoteTerms ctx (t :: ts)
      = (denoteTerm ctx t).bind (fun r => (denoteTerms ctx ts).bind (fun rs => some (r :: rs))) := by
  rfl

/-- `leftAssoc` on exactly two same-typed arguments folds to a single binary application. -/
private theorem leftAssoc_two {ctx : Context} {ty : TermType} {h : (denoteSort ctx.sctx ty).isSome}
    {op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi →
          (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi}
    {r1 r2 : TermDenoteResult ctx} (h1 : r1.ty = ty) (h2 : r2.ty = ty) :
    leftAssoc ctx ty h op [r1, r2]
      = some ⟨ty, h, fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h1 ▸ r1.res tdi) (h2 ▸ r2.res tdi)⟩ := by
  obtain ⟨ty1, hh1, ft1⟩ := r1
  obtain ⟨ty2, hh2, ft2⟩ := r2
  unfold leftAssoc
  dsimp only
  rw [dif_pos h1, dif_pos h2]
  rfl

/-- Unfolding lemma for `denoteTerm` on `and`, exposing the bind + `leftAssoc`. -/
private theorem denoteTerm_and (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.core .and) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (leftAssoc ctx (.prim .bool) rfl (fun _ => And)) := by
  rfl

/-- `chainable` on exactly two same-typed arguments folds to a single binary (`Prop`-valued)
    application, at result sort `.prim .bool`. -/
private theorem chainable_two {ctx : Context} {ty : TermType} {h : (denoteSort ctx.sctx ty).isSome}
    {op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi →
          (denoteSort ctx.sctx ty).get h sdi → Prop}
    {r1 r2 : TermDenoteResult ctx} (h1 : r1.ty = ty) (h2 : r2.ty = ty) :
    chainable ctx ty h op [r1, r2]
      = some ⟨.prim .bool, rfl, fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h1 ▸ r1.res tdi) (h2 ▸ r2.res tdi)⟩ := by
  obtain ⟨ty1, hh1, ft1⟩ := r1
  obtain ⟨ty2, hh2, ft2⟩ := r2
  unfold chainable chainable.go
  dsimp only
  rw [dif_pos h1, dif_pos h2]
  rfl

/-- Unfolding lemma for `denoteTerm` on `eq` (given the two args denote to `r1`, `r2`), exposing
    `chainable` at the first arg's sort. -/
private theorem denoteTerm_eq (ctx : Context) (t1 t2 : Term) (rty : TermType)
    (r1 r2 : TermDenoteResult ctx) (hd : denoteTerms ctx [t1, t2] = some [r1, r2]) :
    denoteTerm ctx (.app (.core .eq) [t1, t2] rty)
      = chainable ctx r1.ty r1.h (fun sdi => @Eq ((denoteSort ctx.sctx r1.ty).get r1.h sdi)) [r1, r2] := by
  simp only [denoteTerm, hd]; rfl

/-- Unfolding lemma for `denoteTerm` on `or`, exposing the bind + `leftAssoc`. -/
private theorem denoteTerm_or (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.core .or) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (leftAssoc ctx (.prim .bool) rfl (fun _ => Or)) := by
  rfl

/-- `rightAssoc` on exactly two same-typed arguments folds to a single binary application. -/
private theorem rightAssoc_two {ctx : Context} {ty : TermType} {h : (denoteSort ctx.sctx ty).isSome}
    {op : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi →
          (denoteSort ctx.sctx ty).get h sdi → (denoteSort ctx.sctx ty).get h sdi}
    {r1 r2 : TermDenoteResult ctx} (h1 : r1.ty = ty) (h2 : r2.ty = ty) :
    rightAssoc ctx ty h op [r1, r2]
      = some ⟨ty, h, fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (h1 ▸ r1.res tdi) (h2 ▸ r2.res tdi)⟩ := by
  obtain ⟨ty1, hh1, ft1⟩ := r1
  obtain ⟨ty2, hh2, ft2⟩ := r2
  unfold rightAssoc rightAssoc.go
  dsimp only
  rw [dif_pos h2, dif_pos h1]
  rfl

/-- Unfolding lemma for `denoteTerm` on `implies`, exposing the bind + `rightAssoc`. -/
private theorem denoteTerm_implies (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.core .implies) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (rightAssoc ctx (.prim .bool) rfl (fun _ p q => p → q)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `add`. -/
private theorem denoteTerm_add (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .add) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind
          (leftAssoc ctx (.prim .int) rfl (fun _ => @HAdd.hAdd Int Int Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `sub`. -/
private theorem denoteTerm_sub (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .sub) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind
          (leftAssoc ctx (.prim .int) rfl (fun _ => @HSub.hSub Int Int Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `mul`. -/
private theorem denoteTerm_mul (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .mul) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind
          (leftAssoc ctx (.prim .int) rfl (fun _ => @HMul.hMul Int Int Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `le`. -/
private theorem denoteTerm_le (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .le) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (chainable ctx (.prim .int) rfl (fun _ => @LE.le Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `lt`. -/
private theorem denoteTerm_lt (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .lt) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (chainable ctx (.prim .int) rfl (fun _ => @LT.lt Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `ge`. -/
private theorem denoteTerm_ge (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .ge) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (chainable ctx (.prim .int) rfl (fun _ => @GE.ge Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `gt`. -/
private theorem denoteTerm_gt (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .gt) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind (chainable ctx (.prim .int) rfl (fun _ => @GT.gt Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on int `div`. -/
private theorem denoteTerm_div (ctx : Context) (t1 t2 : Term) (rty : TermType) :
    denoteTerm ctx (.app (.num .div) [t1, t2] rty)
      = (denoteTerms ctx [t1, t2]).bind
          (leftAssoc ctx (.prim .int) rfl (fun _ => @HDiv.hDiv Int Int Int _)) := by
  rfl

/-- Unfolding lemma for `denoteTerm` on `not`, exposing the monadic bind on the argument. -/
private theorem denoteTerm_not (ctx : Context) (t : Term) (rty : TermType) :
    denoteTerm ctx (.app (.core .not) [t] rty)
      = (denoteTerm ctx t).bind (fun r =>
          match r with
          | ⟨.prim .bool, h, a⟩ => some ⟨.prim .bool, h, fun Γ => ¬ a Γ⟩
          | _ => none) := by
  rfl

/-- **SMT-side quantifier reindexing.** Quantifying the body's denotation over every full environment
    extension of `v0 :: rest` is the same as quantifying over a value for `v0` and then every extension
    of `rest` (the peeled binder is absorbed into the base environment). The membership set is exact
    (`TermVar`), so this holds with no distinctness assumption on the binder list. -/
private theorem smt_combine_reindex_forall {tyctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (v0 : TermVar) (rest : List TermVar) (env : VarEnv σ SmtArrayTheory)
    (body : Term) (hbody : Term.typeCheck tyctx body = .ok .bool) :
    (∀ ext : VarEnv σ SmtArrayTheory,
        Term.denoteTyped ufInterp (fun v => if v ∈ v0 :: rest then ext v else env v)
          (fun _ => 0) id body .bool hbody = true)
      ↔ (∀ (a : TermType.denoteTyped σ SmtArrayTheory v0.ty) (ext : VarEnv σ SmtArrayTheory),
          Term.denoteTyped ufInterp
            (fun v => if v ∈ rest then ext v else (if hv : v = v0 then hv ▸ a else env v))
            (fun _ => 0) id body .bool hbody = true) := by
  constructor
  · intro h a ext
    by_cases hv0 : v0 ∈ rest
    · rw [Term.denoteTyped_env_congr ufInterp _ (fun v => if v ∈ v0 :: rest then ext v else env v)
            (fun _ => 0) id body .bool hbody ?_]
      · exact h ext
      · funext v
        by_cases hvv0 : v = v0
        · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
        · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
    · rw [Term.denoteTyped_env_congr ufInterp _
            (fun v => if v ∈ v0 :: rest then (fun w => if hw : w = v0 then hw ▸ a else ext w) v else env v)
            (fun _ => 0) id body .bool hbody ?_]
      · exact h (fun w => if hw : w = v0 then hw ▸ a else ext w)
      · funext v
        by_cases hvv0 : v = v0
        · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
        · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
  · intro h ext
    rw [Term.denoteTyped_env_congr ufInterp _
          (fun v => if v ∈ rest then ext v else (if hv : v = v0 then hv ▸ ext v0 else env v))
          (fun _ => 0) id body .bool hbody ?_]
    · exact h (ext v0) ext
    · funext v
      by_cases hvv0 : v = v0
      · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
      · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]

/-- Reindexing an existential over environment extensions: quantifying the body's denotation over some
    full environment extension of `v0 :: rest` is equivalent to existentially choosing a value for `v0`
    and then some extension of `rest` (the peeled binder is absorbed into the base environment). -/
private theorem smt_combine_reindex_exists {tyctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (v0 : TermVar) (rest : List TermVar) (env : VarEnv σ SmtArrayTheory)
    (body : Term) (hbody : Term.typeCheck tyctx body = .ok .bool) :
    (∃ ext : VarEnv σ SmtArrayTheory,
        Term.denoteTyped ufInterp (fun v => if v ∈ v0 :: rest then ext v else env v)
          (fun _ => 0) id body .bool hbody = true)
      ↔ (∃ (a : TermType.denoteTyped σ SmtArrayTheory v0.ty) (ext : VarEnv σ SmtArrayTheory),
          Term.denoteTyped ufInterp
            (fun v => if v ∈ rest then ext v else (if hv : v = v0 then hv ▸ a else env v))
            (fun _ => 0) id body .bool hbody = true) := by
  constructor
  · rintro ⟨ext, h⟩
    refine ⟨ext v0, ext, ?_⟩
    rw [Term.denoteTyped_env_congr ufInterp _ (fun v => if v ∈ v0 :: rest then ext v else env v)
          (fun _ => 0) id body .bool hbody ?_]
    · exact h
    · funext v
      by_cases hvv0 : v = v0
      · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
      · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
  · rintro ⟨a, ext, h⟩
    by_cases hv0 : v0 ∈ rest
    · refine ⟨ext, ?_⟩
      rw [Term.denoteTyped_env_congr ufInterp _
            (fun v => if v ∈ rest then ext v else (if hv : v = v0 then hv ▸ a else env v))
            (fun _ => 0) id body .bool hbody ?_]
      · exact h
      · funext v
        by_cases hvv0 : v = v0
        · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
        · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
    · refine ⟨fun w => if hw : w = v0 then hw ▸ a else ext w, ?_⟩
      rw [Term.denoteTyped_env_congr ufInterp _
            (fun v => if v ∈ rest then ext v else (if hv : v = v0 then hv ▸ a else env v))
            (fun _ => 0) id body .bool hbody ?_]
      · exact h
      · funext v
        by_cases hvv0 : v = v0
        · subst hvv0; by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]
        · by_cases hvr : v ∈ rest <;> simp_all [List.mem_cons]

/-- **Quantifier domain bridge.** Two predicates, one over the SMT carrier `TermType.denoteTyped σ SmtArrayTheory ty` and one
    over the `denoteTerm` realization, agree under `∀` provided (i) they agree on `ValEquiv`-related values
    and (ii) `ValEquiv` is total from both sides (`ValEquiv_cover`). This turns the SMT-side `∀ a` into the
    `denoteTerm`-side `∀ x` (and dually for `∃`). -/
private theorem forall_bridge {sctx : SortContext} (ty : TermType)
    (h : (denoteSort sctx ty).isSome) (sdi : SortDenoteInput sctx)
    (P : TermType.denoteTyped σ SmtArrayTheory ty → Prop) (Q : (denoteSort sctx ty).get h sdi → Prop)
    (hPQ : ∀ (a : TermType.denoteTyped σ SmtArrayTheory ty) (x : (denoteSort sctx ty).get h sdi),
        ValEquiv sctx ty a h sdi x → (P a ↔ Q x))
    (hcov1 : ∀ a : TermType.denoteTyped σ SmtArrayTheory ty, ∃ x, ValEquiv sctx ty a h sdi x)
    (hcov2 : ∀ x, ∃ a : TermType.denoteTyped σ SmtArrayTheory ty, ValEquiv sctx ty a h sdi x) :
    (∀ a, P a) ↔ (∀ x, Q x) := by
  constructor
  · intro hP x; obtain ⟨a, ha⟩ := hcov2 x; exact (hPQ a x ha).mp (hP a)
  · intro hQ a; obtain ⟨x, hx⟩ := hcov1 a; exact (hPQ a x hx).mpr (hQ x)

/-- **Existential bridge.** A predicate `P` over the SMT carrier and a predicate `Q` over the
    `denoteTerm` realization agree under `∃` (`(∃ a, P a) ↔ (∃ x, Q x)`) whenever they agree on every
    pair of `ValEquiv`-related values and `ValEquiv` is total from both sides — every SMT value has a
    related realization value and vice versa. -/
private theorem exists_bridge {sctx : SortContext} (ty : TermType)
    (h : (denoteSort sctx ty).isSome) (sdi : SortDenoteInput sctx)
    (P : TermType.denoteTyped σ SmtArrayTheory ty → Prop) (Q : (denoteSort sctx ty).get h sdi → Prop)
    (hPQ : ∀ (a : TermType.denoteTyped σ SmtArrayTheory ty) (x : (denoteSort sctx ty).get h sdi),
        ValEquiv sctx ty a h sdi x → (P a ↔ Q x))
    (hcov1 : ∀ a : TermType.denoteTyped σ SmtArrayTheory ty, ∃ x, ValEquiv sctx ty a h sdi x)
    (hcov2 : ∀ x, ∃ a : TermType.denoteTyped σ SmtArrayTheory ty, ValEquiv sctx ty a h sdi x) :
    (∃ a, P a) ↔ (∃ x, Q x) := by
  constructor
  · rintro ⟨a, hPa⟩; obtain ⟨x, hx⟩ := hcov1 a; exact ⟨x, (hPQ a x hx).mp hPa⟩
  · rintro ⟨x, hQx⟩; obtain ⟨a, ha⟩ := hcov2 x; exact ⟨a, (hPQ a x ha).mpr hQx⟩

/-- Transport-application: a `denoteTerm` body interpretation transported along a body-context list
    equality, then applied, equals the original applied to the back-transported input. -/
private theorem tdi_transport_app {sctx : SortContext} {ufs' : UFContext}
    {L1 L2 : List TermVar} (h : L1 = L2)
    (f : TermDenoteInput ⟨sctx, ⟨L1, ufs'⟩⟩ → Prop) (t : TermDenoteInput ⟨sctx, ⟨L2, ufs'⟩⟩) :
    (h ▸ f) t = f (h ▸ t) := by
  subst h; rfl

/-- `EnvCorr` transports along a body-context list equality. -/
private theorem envcorr_transport {sctx : SortContext} {ufs' : UFContext}
    {L1 L2 : List TermVar} (h : L1 = L2) (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory)
    (t : TermDenoteInput ⟨sctx, ⟨L2, ufs'⟩⟩) (he : EnvCorr ufInterp env t) :
    EnvCorr ufInterp env (h ▸ t) := by
  subst h; exact he

/-- **Universal-quantifier body agreement.** Given that the body denotes agreeably under every
    `EnvCorr`-related environment, the typed denotation's whole-environment `∀ ext` matches `denoteTerm`'s
    per-binder nested `buildForall`. Proved by induction on the binder list. -/
private theorem buildForall_agree {tyctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (body : Term) (hbody : Term.typeCheck tyctx body = .ok .bool) :
    ∀ (vs : List TermVar) {ctx : Context} (env : VarEnv σ SmtArrayTheory) (tdi : TermDenoteInput ctx)
      (_hEnv : EnvCorr ufInterp env tdi)
      (hTys : (denoteFunSort ctx.sctx (vs.map (·.ty)) (.prim .bool)).isSome)
      (bodyFt : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
      (_hbiff : ∀ (env' : VarEnv σ SmtArrayTheory)
          (tdi' : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩),
          EnvCorr ufInterp env' tdi' →
          (Term.denoteTyped ufInterp env' (fun _ => 0) id body .bool hbody = true ↔ bodyFt tdi')),
      (∀ ext : VarEnv σ SmtArrayTheory,
          Term.denoteTyped ufInterp (fun v => if v ∈ vs then ext v else env v)
            (fun _ => 0) id body .bool hbody = true)
        ↔ buildForall ctx vs hTys bodyFt tdi := by
  intro vs
  induction vs with
  | nil =>
    intro ctx env tdi hEnv hTys bodyFt hbiff
    constructor
    · intro h
      have h0 := h env
      rw [Term.denoteTyped_env_congr ufInterp _ env (fun _ => 0) id body .bool hbody
            (by funext v; simp)] at h0
      exact (hbiff env tdi hEnv).mp h0
    · intro h ext
      rw [Term.denoteTyped_env_congr ufInterp _ env (fun _ => 0) id body .bool hbody
            (by funext v; simp)]
      exact (hbiff env tdi hEnv).mpr h
  | cons v0 rest ih =>
    intro ctx env tdi hEnv hTys bodyFt hbiff
    rw [smt_combine_reindex_forall ufInterp v0 rest env body hbody]
    apply forall_bridge v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩
    · intro a x hax
      refine ih (fun v => if hv : v = v0 then hv ▸ a else env v) _ ?extEnv _ _ ?hbiff'
      case extEnv =>
        -- `EnvCorr` for the `bindForallVar`-extended input `tdi' x`.
        -- `hsort` transfers verbatim (same `sctx`/`sΓ`). Two obligations remain.
        refine ⟨?_, ?_, hEnv.hsort⟩
        · intro i hi hfind
          match i, hi, hfind with
          | 0, _, _ =>
            simpa only [List.getElem_cons_zero, dif_pos] using hax
          | j + 1, hi, hfind =>
            have hjlt : j < tdi.tΓ.vs.length := by
              simp only [List.length_cons] at hi; omega
            simp only [List.getElem_cons_succ] at hfind ⊢
            rw [List.findIdx?_cons] at hfind
            split at hfind
            · simp at hfind
            · rename_i hb
              cases hk : ctx.tctx.vs.findIdx? (· == tdi.tΓ.vs[j].var) with
              | none => rw [hk] at hfind; simp at hfind
              | some k =>
                rw [hk] at hfind
                simp only [Option.map_some, Option.some.injEq] at hfind
                have hkj : k = j := by omega
                have hne : tdi.tΓ.vs[j].var ≠ v0 := by
                  intro h; apply hb; rw [h]; simp
                rw [dif_neg hne]
                exact hEnv.hvar j hjlt (hkj ▸ hk)
        · -- huf: `EnvCorr.huf` is value-level (depends on `tdi` only via `⟨tdi.sΓ,tdi.hsΓ⟩` and
          --   `tdi.tΓ.ufs`, both definitionally equal for the `bindForallVar`-extended input),
          --   so it transfers verbatim.
          exact hEnv.huf
      case hbiff' =>
        intro env' tdi' henv'
        have hlist : (v0 :: rest).reverse ++ ctx.tctx.vs = rest.reverse ++ (v0 :: ctx.tctx.vs) := by
          simp [List.reverse_cons]
        rw [tdi_transport_app hlist bodyFt tdi']
        exact hbiff env' (hlist ▸ tdi') (envcorr_transport hlist ufInterp env' tdi' henv')
    · exact (ValEquiv_cover v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩ hEnv.hsort).1
    · exact (ValEquiv_cover v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩ hEnv.hsort).2

/-- **Existential-quantifier body agreement.** Under `EnvCorr`-related environments, the typed
    denotation's whole-environment `∃ ext` matches `denoteTerm`'s per-binder nested `buildExists`.
    Proved by induction on the binder list. -/
private theorem buildExists_agree {tyctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (body : Term) (hbody : Term.typeCheck tyctx body = .ok .bool) :
    ∀ (vs : List TermVar) {ctx : Context} (env : VarEnv σ SmtArrayTheory) (tdi : TermDenoteInput ctx)
      (_hEnv : EnvCorr ufInterp env tdi)
      (hTys : (denoteFunSort ctx.sctx (vs.map (·.ty)) (.prim .bool)).isSome)
      (bodyFt : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
      (_hbiff : ∀ (env' : VarEnv σ SmtArrayTheory)
          (tdi' : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩),
          EnvCorr ufInterp env' tdi' →
          (Term.denoteTyped ufInterp env' (fun _ => 0) id body .bool hbody = true ↔ bodyFt tdi')),
      (∃ ext : VarEnv σ SmtArrayTheory,
          Term.denoteTyped ufInterp (fun v => if v ∈ vs then ext v else env v)
            (fun _ => 0) id body .bool hbody = true)
        ↔ buildExists ctx vs hTys bodyFt tdi := by
  intro vs
  induction vs with
  | nil =>
    intro ctx env tdi hEnv hTys bodyFt hbiff
    constructor
    · rintro ⟨ext, h⟩
      rw [Term.denoteTyped_env_congr ufInterp _ env (fun _ => 0) id body .bool hbody
            (by funext v; simp)] at h
      exact (hbiff env tdi hEnv).mp h
    · intro h
      refine ⟨env, ?_⟩
      rw [Term.denoteTyped_env_congr ufInterp _ env (fun _ => 0) id body .bool hbody
            (by funext v; simp)]
      exact (hbiff env tdi hEnv).mpr h
  | cons v0 rest ih =>
    intro ctx env tdi hEnv hTys bodyFt hbiff
    rw [smt_combine_reindex_exists ufInterp v0 rest env body hbody]
    apply exists_bridge v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩
    · intro a x hax
      refine ih (fun v => if hv : v = v0 then hv ▸ a else env v) _ ?extEnv _ _ ?hbiff'
      case extEnv =>
        refine ⟨?_, ?_, hEnv.hsort⟩
        · intro i hi hfind
          match i, hi, hfind with
          | 0, _, _ =>
            simpa only [List.getElem_cons_zero, dif_pos] using hax
          | j + 1, hi, hfind =>
            have hjlt : j < tdi.tΓ.vs.length := by
              simp only [List.length_cons] at hi; omega
            simp only [List.getElem_cons_succ] at hfind ⊢
            rw [List.findIdx?_cons] at hfind
            split at hfind
            · simp at hfind
            · rename_i hb
              cases hk : ctx.tctx.vs.findIdx? (· == tdi.tΓ.vs[j].var) with
              | none => rw [hk] at hfind; simp at hfind
              | some k =>
                rw [hk] at hfind
                simp only [Option.map_some, Option.some.injEq] at hfind
                have hkj : k = j := by omega
                have hne : tdi.tΓ.vs[j].var ≠ v0 := by
                  intro h; apply hb; rw [h]; simp
                rw [dif_neg hne]
                exact hEnv.hvar j hjlt (hkj ▸ hk)
        · exact hEnv.huf
      case hbiff' =>
        intro env' tdi' henv'
        have hlist : (v0 :: rest).reverse ++ ctx.tctx.vs = rest.reverse ++ (v0 :: ctx.tctx.vs) := by
          simp [List.reverse_cons]
        rw [tdi_transport_app hlist bodyFt tdi']
        exact hbiff env' (hlist ▸ tdi') (envcorr_transport hlist ufInterp env' tdi' henv')
    · exact (ValEquiv_cover v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩ hEnv.hsort).1
    · exact (ValEquiv_cover v0.ty (denoteFunSortCons_isSome hTys).left ⟨tdi.sΓ, tdi.hsΓ⟩ hEnv.hsort).2

/- ═══════════════════════════════════════════════════════════════════════════
   Fundamental lemma: `Term.denoteTyped` agrees with `denoteTerm` on the well-typed fragment.
   (See the theorem docstring below for the precise statement and its assumptions.)

   Note: the statement is conditioned on `denoteTerm ctx tm = some res`, so constructs `denoteTerm`
   doesn't support (e.g. `distinct`) are covered only vacuously.
   ═══════════════════════════════════════════════════════════════════════════ -/

mutual
/-- **Fundamental agreement theorem** (headline result of this file). On every well-typed term
    (`Term.typeCheck tyctx tm = .ok τ`) that `denoteTerm` also interprets (`denoteTerm ctx tm = some res`),
    the total typed denotation `Term.denoteTyped` and the partial `denoteTerm` agree: they assign the same
    sort (`τ = res.ty`), and the two values are related by the `ValEquiv` logical relation (which at `bool`
    is the Bool-reflects-Prop correspondence). Assumes the environments correspond (`EnvCorr`), and pins
    `divByZero`/`modByZero` to `fun _ => 0`/`id` and the array theory to `SmtArrayTheory` so the zero-divisor
    and array cases coincide with `denoteTerm`. -/
theorem Term.denoteTyped_denoteTerm_agree
    {ctx : Context} {ufInterp : UFInterp σ SmtArrayTheory} {env : VarEnv σ SmtArrayTheory} {tdi : TermDenoteInput ctx}
    (hEnv : EnvCorr ufInterp env tdi)
    {tyctx : TypedContext}
    (tm : Term) (τ : TermType) (htc : Term.typeCheck tyctx tm = .ok τ)
    (res : TermDenoteResult ctx) (hden : denoteTerm ctx tm = some res) :
    ∃ (hty : τ = res.ty),
      ValEquiv ctx.sctx res.ty
        -- `(fun _ => 0)` and `id` pin `divByZero`/`modByZero` to the values `denoteTerm` uses
        -- (Lean's total `/`,`%`: `x / 0 = 0`, `x % 0 = x`), so the zero-divisor cases coincide.
        (hty ▸ Term.denoteTyped ufInterp env (fun _ => 0) id tm τ htc)
        res.h ⟨tdi.sΓ, tdi.hsΓ⟩ (res.res tdi) := by
  cases tm with
  | prim p =>
    cases p with
    | bool b =>
      have hτ : τ = .prim .bool := Term.typeCheck_prim_inv htc
      subst hτ
      by_cases hb : b = true
      · subst hb
        simp only [denoteTerm, Option.pure_def, reduceIte, Option.some.injEq] at hden
        subst hden
        refine ⟨rfl, ?_⟩
        simp only [ValEquiv, Term.denoteTyped, toTVal, PrimValEquiv]
        exact iff_of_true True.intro (Eq.mpr (eq_of_heq (cast_heq _ _)) True.intro)
      · simp only [Bool.not_eq_true] at hb
        subst hb
        simp only [denoteTerm, Option.pure_def, reduceIte, reduceCtorEq, Option.some.injEq] at hden
        subst hden
        refine ⟨rfl, ?_⟩
        simp only [ValEquiv, Term.denoteTyped, toTVal, PrimValEquiv]
        exact iff_of_false Bool.false_ne_true (fun hc => Eq.mp (eq_of_heq (cast_heq _ _)) hc)
    | int i =>
      have hτ : τ = .prim .int := Term.typeCheck_prim_inv htc
      subst hτ
      simp only [denoteTerm, Option.pure_def, Option.some.injEq] at hden
      subst hden
      refine ⟨rfl, ?_⟩
      simp only [ValEquiv, Term.denoteTyped, toTVal, PrimValEquiv]
      exact (eq_of_heq (cast_heq _ _)).symm
    | string s =>
      have hτ : τ = .prim .string := Term.typeCheck_prim_inv htc
      subst hτ
      simp only [denoteTerm, Option.pure_def, Option.some.injEq] at hden
      subst hden
      refine ⟨rfl, ?_⟩
      simp only [ValEquiv, Term.denoteTyped, toTVal, PrimValEquiv]
      exact (eq_of_heq (cast_heq _ _)).symm
    | bitvec bv =>
      have hτ : τ = .prim (.bitvec _) := Term.typeCheck_prim_inv htc
      subst hτ
      simp only [denoteTerm, Option.pure_def, Option.some.injEq] at hden
      subst hden
      refine ⟨rfl, ?_⟩
      simp only [ValEquiv, Term.denoteTyped, toTVal, PrimValEquiv]
      exact (eq_of_heq (cast_heq _ _)).symm
    | real r => simp only [denoteTerm, reduceCtorEq] at hden
  | var v =>
    obtain ⟨_, hvτ⟩ := Term.typeCheck_var_inv htc
    subst hvτ
    unfold denoteTerm at hden
    split at hden
    · rename_i hTy
      split at hden
      · rename_i i hfi
        simp only [Option.pure_def, Option.some.injEq] at hden
        subst hden
        refine ⟨rfl, ?_⟩
        have hi : i < ctx.tctx.vs.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hfi).left
        have hivΓ : i < tdi.tΓ.vs.length := tdi.htΓ.hv.h ▸ hi
        have hiv : ctx.tctx.vs[i] = v :=
          eq_of_beq (List.getElem_of_findIdx?_eq_some hfi)
        have hvarv : (tdi.tΓ.vs[i]'hivΓ).var = v := (tdi.htΓ.hv.ha i hi).symm.trans hiv
        have hvar := hEnv.hvar i hivΓ (by rw [hvarv]; exact hfi)
        have hsmt : Term.denoteTyped ufInterp env (fun _ => 0) id (.var v) v.ty htc = env v := by
          apply eq_of_heq
          unfold Term.denoteTyped
          obtain ⟨hmem, heq⟩ := Term.typeCheck_var_inv htc
          simp only
          exact cast_heq _ _
        rw [hsmt]
        exact hvarv ▸ hvar
      · simp at hden
    · simp at hden
  | none ty =>
    have hτ := Term.typeCheck_none_inv htc
    subst hτ
    unfold denoteTerm at hden
    split at hden
    · simp only [Option.pure_def, Option.some.injEq] at hden
      subst hden
      refine ⟨rfl, ?_⟩
      rw [Term.denoteTyped_none]
      simp only [ValEquiv, cast_eq, cast_eqRec_self]
    · simp at hden
  | some t =>
    cases hdt : denoteTerm ctx t with
    | none => simp [denoteTerm, hdt] at hden
    | some rt =>
      obtain ⟨hty_t, hrel_t⟩ := Term.denoteTyped_denoteTerm_agree hEnv t
        (Term.typeCheck_some_inv htc).1 (Term.typeCheck_some_inv htc).2.1 rt hdt
      obtain ⟨rty, rh, rres⟩ := rt
      cases hty_t
      dsimp only at hrel_t
      simp only [denoteTerm, hdt, bind, Option.bind, Option.pure_def, Option.some.injEq] at hden
      subst hden
      refine ⟨(Term.typeCheck_some_inv htc).2.2, ?_⟩
      rw [Term.denoteTyped_some ufInterp env (fun _ => 0) id t τ htc,
        denoteTyped_eqRec_eq_cast]
      simp only [ValEquiv, cast_cast, cast_eq, cast_eqRec_self]
      exact hrel_t
  | app op args rty =>
    cases op with
    | core c =>
      cases c with
      | uf f =>
        have hargs : Term.typeCheckArgs tyctx args f.args = true := by
          simp only [Term.typeCheck] at htc; split at htc <;> (try split at htc) <;> simp_all
        have hout : τ = f.out := by
          simp only [Term.typeCheck] at htc; split at htc <;> (try split at htc) <;> simp_all
        subst hout
        unfold denoteTerm at hden
        split at hden
        · rename_i hTys
          split at hden
          · rename_i i hfi
            cases hda : denoteTerms ctx args with
            | none => rw [hda] at hden; simp at hden
            | some as =>
              rw [hda] at hden
              simp only [Option.bind_eq_bind, Option.bind_some] at hden
              split at hden
              · rename_i hufas
                simp only [Option.pure_def, Option.some.injEq] at hden
                subst hden
                refine ⟨rfl, ?_⟩
                have hi_ctx : i < ctx.tctx.ufs.length :=
                  (List.findIdx?_eq_some_iff_findIdx_eq.mp hfi).left
                have hi_ufs : i < tdi.tΓ.ufs.length := tdi.htΓ.huf.h ▸ hi_ctx
                have hidx : ctx.tctx.ufs[i] = f := eq_of_beq (List.getElem_of_findIdx?_eq_some hfi)
                have hufeq : (tdi.tΓ.ufs[i]'hi_ufs).uf = f :=
                  (tdi.htΓ.huf.ha i hi_ctx).symm.trans hidx
                have argsrel : ArgsEquiv tdi f.args
                    (Term.denoteTypedArgs ufInterp env (fun _ => 0) id args f.args hargs) as :=
                  Term.denoteTypedArgs_denoteTerms_agree hEnv args f.args hargs as hda
                rw [Term.denoteTyped_uf ufInterp env (fun _ => 0) id f args rty f.out htc hargs rfl]
                simp only [cast_eq]
                apply uf_ValEquiv_transport ufInterp f (tdi.tΓ.ufs[i]'hi_ufs).uf hufeq
                  (Term.denoteTypedArgs ufInterp env (fun _ => 0) id args f.args hargs) as hTys
                  (tdi.tΓ.ufs[i]'hi_ufs).h (tdi.tΓ.ufs[i]'hi_ufs).ufΓ hufas
                  (by rw [hufeq])
                exact hEnv.huf i hi_ufs
                  (hufeq.symm ▸ (Term.denoteTypedArgs ufInterp env (fun _ => 0) id args f.args hargs))
                  (as.map (fun a => ⟨a.ty, a.h, a.res tdi⟩))
                  (hufeq.symm ▸ argTypesAlign_to_valTypesAlign tdi as f.args hufas)
                  (hufeq.symm ▸ argsRel_to_argsValEquiv tdi f.args
                    (Term.denoteTypedArgs ufInterp env (fun _ => 0) id args f.args hargs) as argsrel)
              · simp at hden
          · simp at hden
        · simp at hden
      | not =>
        match args, htc with
        | [t], htc =>
          obtain ⟨ht, hτ⟩ := Term.typeCheck_not_inv htc
          subst hτ
          rw [denoteTerm_not] at hden
          cases hda : denoteTerm ctx t with
          | none => rw [hda] at hden; simp at hden
          | some ares =>
            rw [hda] at hden
            obtain ⟨hty_a, hrel⟩ := Term.denoteTyped_denoteTerm_agree hEnv t .bool ht ares hda
            obtain ⟨aty, ah, af⟩ := ares
            cases hty_a
            simp only [Option.bind_some, Option.some.injEq] at hden
            subst hden
            refine ⟨rfl, ?_⟩
            simp only [ValEquiv, PrimValEquiv] at hrel ⊢
            rw [Term.denoteTyped_not ufInterp env (fun _ => 0) id t rty .bool htc, cast_eq]
            have hc : toTVal ctx.sctx (.prim .bool) ah ⟨tdi.sΓ, tdi.hsΓ⟩ (af tdi) = af tdi :=
              eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)
            rw [hc] at hrel
            rw [show toTVal ctx.sctx (.prim .bool) ah ⟨tdi.sΓ, tdi.hsΓ⟩ (¬ af tdi) = ¬ af tdi from
              eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
            rw [← hrel]
            cases Term.denoteTyped ufInterp env (fun _ => 0) id t .bool (Term.typeCheck_not_inv htc).1 <;> simp
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | and =>
        match args, htc with
        | [t1, t2], htc =>
          obtain ⟨h1, h2, hτ⟩ := Term.typeCheck_boolBin_inv htc (.inl rfl)
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_and, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_and, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ := Term.denoteTyped_denoteTerm_agree hEnv t1 .bool h1 r1 hd1
              obtain ⟨hty2, hrel2⟩ := Term.denoteTyped_denoteTerm_agree hEnv t2 .bool h2 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .bool, ah1, af1⟩, ⟨.prim .bool, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_and, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .bool) _ (fun _ => And)
                  ⟨.prim .bool, ah1, af1⟩ ⟨.prim .bool, ah2, af2⟩ rfl rfl,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv] at hrel1 hrel2 ⊢
              rw [Term.denoteTyped_and ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) ah1 ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi) = af1 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel1
              rw [show toTVal ctx.sctx (.prim .bool) ah2 ⟨tdi.sΓ, tdi.hsΓ⟩ (af2 tdi) = af2 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel2
              have hkey1 : (Term.denoteTyped ufInterp env (fun _ => 0) id t1 .bool
                  (Term.typeCheck_boolBin_inv htc (.inl rfl)).1 = true) ↔ af1 tdi := hrel1
              have hkey2 : (Term.denoteTyped ufInterp env (fun _ => 0) id t2 .bool
                  (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1 = true) ↔ af2 tdi := hrel2
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi ∧ af2 tdi)
                    = (af1 tdi ∧ af2 tdi) from eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              rw [Bool.and_eq_true, hkey1, hkey2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | or =>
        match args, htc with
        | [t1, t2], htc =>
          obtain ⟨h1, h2, hτ⟩ := Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_or, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_or, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ := Term.denoteTyped_denoteTerm_agree hEnv t1 .bool h1 r1 hd1
              obtain ⟨hty2, hrel2⟩ := Term.denoteTyped_denoteTerm_agree hEnv t2 .bool h2 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .bool, ah1, af1⟩, ⟨.prim .bool, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_or, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .bool) _ (fun _ => Or)
                  ⟨.prim .bool, ah1, af1⟩ ⟨.prim .bool, ah2, af2⟩ rfl rfl,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv] at hrel1 hrel2 ⊢
              rw [Term.denoteTyped_or ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) ah1 ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi) = af1 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel1
              rw [show toTVal ctx.sctx (.prim .bool) ah2 ⟨tdi.sΓ, tdi.hsΓ⟩ (af2 tdi) = af2 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel2
              have hkey1 : (Term.denoteTyped ufInterp env (fun _ => 0) id t1 .bool
                  (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1 = true) ↔ af1 tdi := hrel1
              have hkey2 : (Term.denoteTyped ufInterp env (fun _ => 0) id t2 .bool
                  (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1 = true) ↔ af2 tdi := hrel2
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi ∨ af2 tdi)
                    = (af1 tdi ∨ af2 tdi) from eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              rw [Bool.or_eq_true, hkey1, hkey2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | eq =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .bool := (Term.typeCheck_eq_inv htc).2.2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => simp [denoteTerm, denoteTerms_cons, hd1] at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none => simp [denoteTerm, denoteTerms_cons, hd1, hd2] at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨(Term.typeCheck_eq_inv htc).1, ah1, af1⟩, ⟨(Term.typeCheck_eq_inv htc).1, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_eq ctx t1 t2 rty ⟨(Term.typeCheck_eq_inv htc).1, ah1, af1⟩
                    ⟨(Term.typeCheck_eq_inv htc).1, ah2, af2⟩ hdts,
                @chainable_two ctx (Term.typeCheck_eq_inv htc).1 ah1
                  (fun sdi => @Eq ((denoteSort ctx.sctx (Term.typeCheck_eq_inv htc).1).get ah1 sdi))
                  ⟨(Term.typeCheck_eq_inv htc).1, ah1, af1⟩ ⟨(Term.typeCheck_eq_inv htc).1, ah2, af2⟩ rfl rfl,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv]
              rw [Term.denoteTyped_eq ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi = af2 tdi)
                    = (af1 tdi = af2 tdi) from eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              simp only [decide_eq_true_eq]
              exact ValEquiv_eq_iff hEnv.hsort hrel1 hrel2
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | ite =>
        match args, htc with
        | [c, t, e], htc =>
          obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc
          cases hdc : denoteTerm ctx c with
          | none => simp [denoteTerm, hdc] at hden
          | some rc =>
            obtain ⟨htyc, hrelc⟩ := Term.denoteTyped_denoteTerm_agree hEnv c .bool hc rc hdc
            obtain ⟨cty, chp, cfp⟩ := rc
            cases htyc
            cases hdt : denoteTerm ctx t with
            | none => simp [denoteTerm, hdc, hdt] at hden
            | some rt =>
              cases hde : denoteTerm ctx e with
              | none => simp [denoteTerm, hdc, hdt, hde] at hden
              | some re =>
                obtain ⟨htyt, hrelt⟩ := Term.denoteTyped_denoteTerm_agree hEnv t τ ht rt hdt
                obtain ⟨htye, hrele⟩ := Term.denoteTyped_denoteTerm_agree hEnv e τ he re hde
                obtain ⟨tty, thp, tfp⟩ := rt
                obtain ⟨ety, ehp, efp⟩ := re
                cases htyt; cases htye
                dsimp only at hrelt hrele
                simp only [denoteTerm, hdc, hdt, hde, bind, Option.bind, dif_pos, Option.pure_def,
                  Option.some.injEq] at hden
                subst hden
                refine ⟨rfl, ?_⟩
                rw [Term.denoteTyped_ite ufInterp env (fun _ => 0) id c t e rty _ htc]
                have hrelc' : (Term.denoteTyped ufInterp env (fun _ => 0) id c .bool (Term.typeCheck_ite_inv htc).1
                    = true) ↔ cfp tdi := ValEquiv_bool_elim (HEq.refl _) hrelc
                cases hsc : Term.denoteTyped ufInterp env (fun _ => 0) id c .bool (Term.typeCheck_ite_inv htc).1 with
                | true =>
                  simp only [cond_true]
                  rw [if_pos (hrelc'.mp hsc)]
                  exact hrelt
                | false =>
                  simp only [cond_false]
                  rw [if_neg (fun hcfp => by simp [hrelc'.mpr hcfp] at hsc)]
                  exact hrele
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_, _], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | implies =>
        match args, htc with
        | [t1, t2], htc =>
          obtain ⟨h1, h2, hτ⟩ := Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_implies, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_implies, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden
              simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ := Term.denoteTyped_denoteTerm_agree hEnv t1 .bool h1 r1 hd1
              obtain ⟨hty2, hrel2⟩ := Term.denoteTyped_denoteTerm_agree hEnv t2 .bool h2 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .bool, ah1, af1⟩, ⟨.prim .bool, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_implies, hdts, Option.bind_some,
                @rightAssoc_two ctx (.prim .bool) _ (fun _ p q => p → q)
                  ⟨.prim .bool, ah1, af1⟩ ⟨.prim .bool, ah2, af2⟩ rfl rfl,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv] at hrel1 hrel2 ⊢
              rw [Term.denoteTyped_implies ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) ah1 ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi) = af1 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel1
              rw [show toTVal ctx.sctx (.prim .bool) ah2 ⟨tdi.sΓ, tdi.hsΓ⟩ (af2 tdi) = af2 tdi from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)] at hrel2
              have hkey1 : (Term.denoteTyped ufInterp env (fun _ => 0) id t1 .bool
                  (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1 = true) ↔ af1 tdi := hrel1
              have hkey2 : (Term.denoteTyped ufInterp env (fun _ => 0) id t2 .bool
                  (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1 = true) ↔ af2 tdi := hrel2
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩ (af1 tdi → af2 tdi)
                    = (af1 tdi → af2 tdi) from eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              rw [← hkey1, ← hkey2]
              cases Term.denoteTyped ufInterp env (fun _ => 0) id t1 .bool
                    (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1 <;>
                cases Term.denoteTyped ufInterp env (fun _ => 0) id t2 .bool
                    (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1 <;> simp
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | distinct =>
        -- `denoteTerm` has no `distinct` case (returns `none`), so this is vacuous.
        simp only [denoteTerm, reduceCtorEq] at hden
    | num n =>
      cases n with
      | neg =>
        match args, htc with
        | [t], htc =>
          have hτ : τ = .int := (Term.typeCheck_intUn_inv htc).2
          subst hτ
          cases hdt : denoteTerm ctx t with
          | none => simp [denoteTerm, hdt] at hden
          | some rt =>
            obtain ⟨htyt, hrelt⟩ :=
              Term.denoteTyped_denoteTerm_agree hEnv t .int (Term.typeCheck_intUn_inv htc).1 rt hdt
            obtain ⟨tty, thp, tfp⟩ := rt
            cases htyt
            dsimp only at hrelt
            simp only [denoteTerm, hdt, bind, Option.bind, Option.pure_def, Option.some.injEq] at hden
            subst hden
            refine ⟨rfl, ?_⟩
            apply ValEquiv_int_mk
            rw [Term.denoteTyped_neg ufInterp env (fun _ => 0) id t rty .int htc, ValEquiv_int_get hrelt]
            exact eq_of_heq (cast_heq _ _)
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | add =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .int := (Term.typeCheck_intBin_inv htc (.inl rfl)).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_add, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_add, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_add, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .int) _ (fun _ => @HAdd.hAdd Int Int Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_int_mk
              rw [Term.denoteTyped_add ufInterp env (fun _ => 0) id t1 t2 rty .int htc, cast_eq,
                ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | sub =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .int := (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_sub, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_sub, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_sub, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .int) _ (fun _ => @HSub.hSub Int Int Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_int_mk
              rw [Term.denoteTyped_sub ufInterp env (fun _ => 0) id t1 t2 rty .int htc, cast_eq,
                ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | mul =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_mul, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_mul, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_mul, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .int) _ (fun _ => @HMul.hMul Int Int Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_int_mk
              rw [Term.denoteTyped_mul ufInterp env (fun _ => 0) id t1 t2 rty .int htc, cast_eq,
                ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | div =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_div, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_div, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_div, hdts, Option.bind_some,
                @leftAssoc_two ctx (.prim .int) _ (fun _ => @HDiv.hDiv Int Int Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_int_mk
              rw [Term.denoteTyped_div ufInterp env (fun _ => 0) id t1 t2 rty .int htc, cast_eq]
              simp only [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
              split <;> simp_all
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | rdiv => simp only [Term.typeCheck, reduceCtorEq] at htc
      | mod =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .int := (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => simp only [denoteTerm, hd1, bind, Option.bind, reduceCtorEq] at hden
          | some r1 =>
            obtain ⟨hty1, hrel1⟩ :=
              Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 r1 hd1
            obtain ⟨aty1, ah1, af1⟩ := r1
            cases hty1
            dsimp only at hrel1
            cases hd2 : denoteTerm ctx t2 with
            | none => simp only [denoteTerm, hd1, hd2, bind, Option.bind, reduceCtorEq] at hden
            | some r2 =>
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 r2 hd2
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty2
              dsimp only at hrel2
              simp only [denoteTerm, hd1, hd2, bind, Option.bind, Option.pure_def,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_int_mk
              rw [Term.denoteTyped_mod ufInterp env (fun _ => 0) id t1 t2 rty .int htc, cast_eq]
              simp only [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
              split <;> simp_all
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | abs => simp only [Term.typeCheck, reduceCtorEq] at htc
      | le =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .bool := (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_le, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_le, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_le, hdts, Option.bind_some,
                @chainable_two ctx (.prim .int) _ (fun _ => @LE.le Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv]
              rw [Term.denoteTyped_le ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩
                      (@LE.le Int _ (af1 tdi) (af2 tdi))
                    = (@LE.le Int _ (af1 tdi) (af2 tdi)) from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              simp only [decide_eq_true_eq]
              rw [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | lt =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_lt, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_lt, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_lt, hdts, Option.bind_some,
                @chainable_two ctx (.prim .int) _ (fun _ => @LT.lt Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv]
              rw [Term.denoteTyped_lt ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩
                      (@LT.lt Int _ (af1 tdi) (af2 tdi))
                    = (@LT.lt Int _ (af1 tdi) (af2 tdi)) from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              simp only [decide_eq_true_eq]
              rw [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | ge =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_ge, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_ge, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_ge, hdts, Option.bind_some,
                @chainable_two ctx (.prim .int) _ (fun _ => @GE.ge Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv]
              rw [Term.denoteTyped_ge ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩
                      (@GE.ge Int _ (af1 tdi) (af2 tdi))
                    = (@GE.ge Int _ (af1 tdi) (af2 tdi)) from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              simp only [decide_eq_true_eq]
              rw [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | gt =>
        match args, htc with
        | [t1, t2], htc =>
          have hτ : τ = .bool := (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2
          subst hτ
          cases hd1 : denoteTerm ctx t1 with
          | none => rw [denoteTerm_gt, denoteTerms_cons, hd1] at hden; simp at hden
          | some r1 =>
            cases hd2 : denoteTerm ctx t2 with
            | none =>
              rw [denoteTerm_gt, denoteTerms_cons, hd1, denoteTerms_cons, hd2] at hden; simp at hden
            | some r2 =>
              obtain ⟨hty1, hrel1⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 r1 hd1
              obtain ⟨hty2, hrel2⟩ :=
                Term.denoteTyped_denoteTerm_agree hEnv t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1 r2 hd2
              obtain ⟨aty1, ah1, af1⟩ := r1
              obtain ⟨aty2, ah2, af2⟩ := r2
              cases hty1; cases hty2
              dsimp only at hrel1 hrel2
              have hdts : denoteTerms ctx [t1, t2]
                  = some [⟨.prim .int, ah1, af1⟩, ⟨.prim .int, ah2, af2⟩] := by
                rw [denoteTerms_cons, hd1, denoteTerms_cons, hd2]; rfl
              rw [denoteTerm_gt, hdts, Option.bind_some,
                @chainable_two ctx (.prim .int) _ (fun _ => @GT.gt Int _)
                  ⟨.prim .int, ah1, af1⟩ ⟨.prim .int, ah2, af2⟩ rfl rfl, Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              simp only [ValEquiv, PrimValEquiv]
              rw [Term.denoteTyped_gt ufInterp env (fun _ => 0) id t1 t2 rty .bool htc, cast_eq]
              rw [show toTVal ctx.sctx (.prim .bool) _ ⟨tdi.sΓ, tdi.hsΓ⟩
                      (@GT.gt Int _ (af1 tdi) (af2 tdi))
                    = (@GT.gt Int _ (af1 tdi) (af2 tdi)) from
                    eq_of_heq (by simp only [toTVal]; exact cast_heq _ _)]
              simp only [decide_eq_true_eq]
              rw [ValEquiv_int_get hrel1, ValEquiv_int_get hrel2]
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
    | bv b => simp only [Term.typeCheck, reduceCtorEq] at htc
    | str s => simp only [Term.typeCheck, reduceCtorEq] at htc
    | arr a =>
      cases a with
      | select =>
        match args, htc with
        | [xt, it], htc =>
          cases hdx : denoteTerm ctx xt with
          | none => simp [denoteTerm, hdx] at hden
          | some xres =>
            obtain ⟨hty_x, hrel_x⟩ := Term.denoteTyped_denoteTerm_agree hEnv xt
              (.constr "Array" [(Term.typeCheck_select_inv htc).1, (Term.typeCheck_select_inv htc).2.1])
              (Term.typeCheck_select_inv htc).2.2.1 xres hdx
            obtain ⟨xty, xh, xf⟩ := xres
            cases hty_x
            dsimp only at hrel_x
            cases hdi : denoteTerm ctx it with
            | none => simp [denoteTerm, hdx, hdi] at hden
            | some ires =>
              obtain ⟨hty_i, hrel_i⟩ := Term.denoteTyped_denoteTerm_agree hEnv it
                (Term.typeCheck_select_inv htc).1 (Term.typeCheck_select_inv htc).2.2.2.1 ires hdi
              obtain ⟨ity, ih, iff'⟩ := ires
              cases hty_i
              dsimp only at hrel_i
              simp only [denoteTerm, hdx, hdi, bind, Option.bind, Option.pure_def, ↓reduceDIte,
                Option.some.injEq] at hden
              subst hden
              refine ⟨(Term.typeCheck_select_inv htc).2.2.2.2.2, ?_⟩
              rw [Term.denoteTyped_select ufInterp env (fun _ => 0) id xt it rty τ htc,
                denoteTyped_eqRec_eq_cast]
              simp only [cast_cast, cast_eq]
              exact hrel_x (Term.denoteTyped ufInterp env (fun _ => 0) id it
                (Term.typeCheck_select_inv htc).1 (Term.typeCheck_select_inv htc).2.2.2.1)
                (iff' tdi) hrel_i
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
      | store =>
        match args, htc with
        | [xt, it, et], htc =>
          cases hdx : denoteTerm ctx xt with
          | none => simp [denoteTerm, hdx] at hden
          | some xres =>
            obtain ⟨hty_x, hrel_x⟩ := Term.denoteTyped_denoteTerm_agree hEnv xt
              (.constr "Array" [(Term.typeCheck_store_inv htc).1, (Term.typeCheck_store_inv htc).2.1])
              (Term.typeCheck_store_inv htc).2.2.1 xres hdx
            obtain ⟨xty, xh, xf⟩ := xres
            cases hty_x
            dsimp only at hrel_x
            cases hdi : denoteTerm ctx it with
            | none => simp [denoteTerm, hdx, hdi] at hden
            | some ires =>
              obtain ⟨hty_i, hrel_i⟩ := Term.denoteTyped_denoteTerm_agree hEnv it
                (Term.typeCheck_store_inv htc).1 (Term.typeCheck_store_inv htc).2.2.2.1 ires hdi
              obtain ⟨ity, ih, iff'⟩ := ires
              cases hty_i
              dsimp only at hrel_i
              cases hde : denoteTerm ctx et with
              | none => simp [denoteTerm, hdx, hdi, hde] at hden
              | some eres =>
                obtain ⟨hty_e, hrel_e⟩ := Term.denoteTyped_denoteTerm_agree hEnv et
                  (Term.typeCheck_store_inv htc).2.1 (Term.typeCheck_store_inv htc).2.2.2.2.1 eres hde
                obtain ⟨ety, eh, ef⟩ := eres
                cases hty_e
                dsimp only at hrel_e
                simp only [denoteTerm, hdx, hdi, hde, bind, Option.bind, Option.pure_def,
                  and_self, ↓reduceDIte, Option.some.injEq] at hden
                subst hden
                refine ⟨(Term.typeCheck_store_inv htc).2.2.2.2.2.2, ?_⟩
                rw [Term.denoteTyped_store ufInterp env (fun _ => 0) id xt it et rty τ htc,
                  denoteTyped_eqRec_eq_cast]
                simp only [cast_cast, cast_eq]
                -- Array extensional relation: relate `store.select` on both sides, casing on the key.
                simp only [ValEquiv, cast_eqRec_self]
                intro ka kb hkab
                have hcond : (ka = Term.denoteTyped ufInterp env (fun _ => 0) id it
                    (Term.typeCheck_store_inv htc).1 (Term.typeCheck_store_inv htc).2.2.2.1)
                    ↔ (kb = iff' tdi) := ValEquiv_eq_iff hEnv.hsort hkab hrel_i
                by_cases hc : ka = Term.denoteTyped ufInterp env (fun _ => 0) id it
                    (Term.typeCheck_store_inv htc).1 (Term.typeCheck_store_inv htc).2.2.2.1
                · -- queried key IS the stored key on both sides
                  rw [hc, @SmtArray.select_store_self _ _ (Classical.typeDecidableEq _),
                      hcond.mp hc, @SmtArray.select_store_self _ _ (Classical.typeDecidableEq _)]
                  exact hrel_e
                · -- queried key differs: both reduce to the underlying array
                  rw [@SmtArray.select_store_of_ne _ _ (Classical.typeDecidableEq _) _ _ _ _ hc,
                      @SmtArray.select_store_of_ne _ _ (Classical.typeDecidableEq _) _ _ _ _
                        (fun heq => hc (hcond.mpr heq))]
                  exact hrel_x ka kb hkab
        | [], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | [_, _], htc => simp only [Term.typeCheck, reduceCtorEq] at htc
        | _ :: _ :: _ :: _ :: _, htc => simp only [Term.typeCheck, reduceCtorEq] at htc
    | option_get => simp only [Term.typeCheck, reduceCtorEq] at htc
    | datatype_op d s => simp only [Term.typeCheck, reduceCtorEq] at htc
  | quant k vs tr body =>
    -- `res.res tdi = buildForall/buildExists ctx vs hTys tFt tdi` (nested per-binder `∀/∃`); the typed
    -- side is a single `∀/∃ ext : VarEnv σ SmtArrayTheory` (`Term.denoteTyped_{forall,exists}_eq_true`).
    -- Bridge them with `buildForall_agree`/`buildExists_agree`.
    obtain ⟨hbody, hτ⟩ := Term.typeCheck_quant_inv htc
    subst hτ
    cases k with
    | all =>
      unfold denoteTerm at hden
      split at hden
      · rename_i hTys
        cases hdb : denoteTerm ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ body with
        | none => simp [hdb] at hden
        | some rb =>
          obtain ⟨rbty, rbh, tFt⟩ := rb
          cases rbty with
          | prim pp =>
            cases pp with
            | bool =>
              simp only [hdb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_bool_mk (HEq.refl _)
              rw [Term.denoteTyped_forall_eq_true ufInterp env (fun _ => 0) id vs tr body htc hbody]
              exact buildForall_agree ufInterp body hbody vs env tdi hEnv hTys tFt
                (fun env' tdi' hEnv' => by
                  obtain ⟨hty', hrel'⟩ :=
                    Term.denoteTyped_denoteTerm_agree hEnv' body .bool hbody ⟨.prim .bool, rbh, tFt⟩ hdb
                  exact ValEquiv_bool_elim (HEq.refl _) hrel')
            | int => simp [hdb] at hden
            | string => simp [hdb] at hden
            | bitvec n => simp [hdb] at hden
            | real => simp [hdb] at hden
            | regex => simp [hdb] at hden
          | option _ => simp [hdb] at hden
          | constr _ _ => simp [hdb] at hden
      · simp at hden
    | exist =>
      unfold denoteTerm at hden
      split at hden
      · rename_i hTys
        cases hdb : denoteTerm ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ body with
        | none => simp [hdb] at hden
        | some rb =>
          obtain ⟨rbty, rbh, tFt⟩ := rb
          cases rbty with
          | prim pp =>
            cases pp with
            | bool =>
              simp only [hdb, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq] at hden
              subst hden
              refine ⟨rfl, ?_⟩
              apply ValEquiv_bool_mk (HEq.refl _)
              rw [Term.denoteTyped_exists_eq_true ufInterp env (fun _ => 0) id vs tr body htc hbody]
              exact buildExists_agree ufInterp body hbody vs env tdi hEnv hTys tFt
                (fun env' tdi' hEnv' => by
                  obtain ⟨hty', hrel'⟩ :=
                    Term.denoteTyped_denoteTerm_agree hEnv' body .bool hbody ⟨.prim .bool, rbh, tFt⟩ hdb
                  exact ValEquiv_bool_elim (HEq.refl _) hrel')
            | int => simp [hdb] at hden
            | string => simp [hdb] at hden
            | bitvec n => simp [hdb] at hden
            | real => simp [hdb] at hden
            | regex => simp [hdb] at hden
          | option _ => simp [hdb] at hden
          | constr _ _ => simp [hdb] at hden
      · simp at hden

/-- Argument-list agreement: when a term-argument list type-checks against `argTys` (`typeCheckArgs`)
    and `denoteTerms` interprets it (`= some ress`), the typed semantics' argument `HList` and the partial
    semantics' argument list `ress` are pointwise related by `ValEquiv` (packaged as `ArgsEquiv`). -/
theorem Term.denoteTypedArgs_denoteTerms_agree
    {ctx : Context} {ufInterp : UFInterp σ SmtArrayTheory} {env : VarEnv σ SmtArrayTheory} {tdi : TermDenoteInput ctx}
    (hEnv : EnvCorr ufInterp env tdi)
    {tyctx : TypedContext}
    (args : List Term) (argTys : List TermType)
    (htc : Term.typeCheckArgs tyctx args argTys = true)
    (ress : List (TermDenoteResult ctx))
    (hden : denoteTerms ctx args = some ress) :
    ArgsEquiv tdi argTys
      (Term.denoteTypedArgs ufInterp env (fun _ => 0) id args argTys htc) ress := by
  cases args with
  | nil =>
    cases argTys with
    | nil =>
      simp only [denoteTerms, Option.pure_def, Option.some.injEq] at hden
      subst hden
      exact True.intro
    | cons ty tys => simp only [Term.typeCheckArgs, reduceCtorEq] at htc
  | cons t ts =>
    cases argTys with
    | nil => simp only [Term.typeCheckArgs, reduceCtorEq] at htc
    | cons ty tys =>
      have hhd : Term.typeCheck tyctx t = .ok ty := by
        simp only [Term.typeCheckArgs] at htc
        split at htc
        · rename_i tty heqt
          simp only [Bool.and_eq_true, beq_iff_eq] at htc
          rw [htc.1] at heqt; exact heqt
        · exact absurd htc (by simp)
      have hrest : Term.typeCheckArgs tyctx ts tys = true := by
        simp only [Term.typeCheckArgs] at htc
        split at htc
        · simp only [Bool.and_eq_true, beq_iff_eq] at htc; exact htc.2
        · exact absurd htc (by simp)
      cases hdt : denoteTerm ctx t with
      | none => rw [denoteTerms_cons, hdt] at hden; simp at hden
      | some r =>
        cases hdts : denoteTerms ctx ts with
        | none => rw [denoteTerms_cons, hdt, hdts] at hden; simp at hden
        | some rs =>
          rw [denoteTerms_cons, hdt, hdts] at hden
          simp only [Option.bind_some, Option.some.injEq] at hden
          subst hden
          exact ⟨Term.denoteTyped_denoteTerm_agree hEnv t ty hhd r hdt,
                 Term.denoteTypedArgs_denoteTerms_agree hEnv ts tys hrest rs hdts⟩
end

end Strata.SMT.DenoteTyped
