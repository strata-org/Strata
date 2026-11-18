/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.FundProof

/-!
# Related programs and their indices

This file defines when two Laurel programs are related up to a term relation `E`, and
proves that related programs build related program indices, so that two runs of related
programs start in related states.

* `ProgRel E p q`: `q`'s procedures, functions, fields, types, constants and heap fields
  correspond to `p`'s, related by `ProcRel`, `FieldDeclRel`, `TypeRel` and `ConstsRel`.
  `q` may have extra procedures, but only with reserved names.
* `ProgRel0`: a variant of `ProgRel` without extra procedures.
* `MapRel`, `MapRelU`: hash maps related key by key.
* `ProgRel0.index`, `ProgRel.index`: `buildIndex p` and `buildIndex q` are related by
  `IxRel0 E` and `IxRel E`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

section
variable [Reserved] (E : StmtExprMd → StmtExprMd → Prop)

def FieldDeclRel (f f' : Field) : Prop :=
  f.name = f'.name ∧ Reserved.tyR f.type.val f'.type.val ∧ ORel E f.initializer f'.initializer ∧ FinOK f.initializer ∧
    OV E f.initializer f'.initializer

structure CompRel (ct ct' : CompositeType) : Prop where
  name : ct.name = ct'.name
  extending : ct.extending = ct'.extending
  fields : L2 (FieldDeclRel E) ct.fields ct'.fields
  procs : ¬ Reserved.resMethods → L2 (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)
    ct.instanceProcedures ct'.instanceProcedures

structure ConsRel (c c' : ConstrainedType) : Prop where
  name : c.name = c'.name
  base : Reserved.tyR c.base.val c'.base.val
  valueName : c.valueName = c'.valueName
  constraint : E c.constraint c'.constraint
  witness : E c.witness c'.witness
  literal : literalValue? c.witness.val = literalValue? c'.witness.val
  vname : ¬ Reserved.res c.valueName.text
  vnameV : NotV c.valueName.text
  constraintOK : Hered FinP c.constraint
  witnessOK : Hered FinP c.witness
  constraintV : Reserved.vok E c.constraint c'.constraint := by trivial
  witnessV : Reserved.vok E c.witness c'.witness := by trivial

def CtorRel (c c' : DatatypeConstructor) : Prop := c.name = c'.name ∧ L2 ParamR c.args c'.args

def DtRel (d d' : DatatypeDefinition) : Prop := d.name = d'.name ∧ L2 CtorRel d.constructors d'.constructors

inductive TypeRel : TypeDefinition → TypeDefinition → Prop where
  | composite {ct ct' : CompositeType} : CompRel E ct ct' → TypeRel (.Composite ct) (.Composite ct')
  | constrained {c c' : ConstrainedType} : ConsRel E c c' → TypeRel (.Constrained c) (.Constrained c')
  | datatype {d d' : DatatypeDefinition} : DtRel d d' → TypeRel (.Datatype d) (.Datatype d')
  | opaque_ (o : OpaqueTypeDefinition) : TypeRel (.Opaque o) (.Opaque o)
  | alias (a : TypeAlias) : TypeRel (.Alias a) (.Alias a)

def RenOK (p : LaurelProgram) : Prop :=
  ∀ f f', Reserved.ren f f' → f'.uniqueId = f.uniqueId ∧
    ∃ id P, f.uniqueId = some id ∧ P ∈ p.staticProcedures ∧ P.name.uniqueId = some id

def ConstsRel (p q : LaurelProgram) : Prop :=
  ∃ cs extra, q.constants = cs ++ extra ∧ L2 (fun c c' => c.name.text = c'.name.text ∧ ConstRel E c c') p.constants cs ∧
    ∀ x ∈ extra, Reserved.resProc x.name.text

def AliasOK (p q : LaurelProgram) : Prop :=
  ∀ t t', Reserved.tyR t t' → unaliasWith (buildAliasMap q.types) t' = unaliasWith (buildAliasMap p.types) t

def HeapKeys (p : LaurelProgram) : List (String × String × HighType) :=
  p.heapFields.map fun f => (f.name.text, f.location.text, f.type.val)

structure ProgRel (p q : LaurelProgram) : Prop where
  procs : ∃ ps extra, q.staticProcedures = ps ++ extra ∧ L2 (ProcRel E) p.staticProcedures ps ∧
    ∀ x ∈ extra, Reserved.resProc x.name.text ∧ x.name.uniqueId = none
  fields : L2 (FieldDeclRel E) p.staticFields q.staticFields
  types : L2 (TypeRel E) (nonAliasTypes p.types) (nonAliasTypes q.types)
  noGlobals : Reserved.noGlobals → p.staticFields = []
  renOK : RenOK p
  funs : L2 (ProcRel E) p.staticFunctions q.staticFunctions
  ixX : Reserved.ixX E (buildIndex p) (buildIndex q)
  outG : ∀ o, Reserved.vret = some o → ∀ f ∈ p.staticFields, f.name.text ≠ o
  consts : ConstsRel E p q
  unalias : AliasOK p q
  heapFields : HeapKeys q = HeapKeys p
  heapTy : ∀ k ∈ HeapKeys p, Reserved.tyR k.2.2 k.2.2

structure ProgRel0 (p q : LaurelProgram) : Prop where
  procs : L2 (ProcRel E) (p.staticFunctions ++ p.staticProcedures) (q.staticFunctions ++ q.staticProcedures)
  types : L2 (TypeRel E) (nonAliasTypes p.types) (nonAliasTypes q.types)
  renOK : RenOK p
  consts : ConstsRel E p q
  unalias : AliasOK p q
  heapFields : HeapKeys q = HeapKeys p
  heapTy : ∀ k ∈ HeapKeys p, Reserved.tyR k.2.2 k.2.2

end

theorem L2.foldl_rel {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l')
    {F : δ → α → δ} {G : ε → β → ε} {Inv : δ → ε → Prop}
    (hF : ∀ acc acc' a b, Inv acc acc' → R a b → Inv (F acc a) (G acc' b)) {init : δ} {init' : ε}
    (hi : Inv init init') : Inv (l.foldl F init) (l'.foldl G init') := by
  induction h generalizing init init' with
  | nil => exact hi
  | cons hab _ ih => exact ih (hF _ _ _ _ hi hab)

def MapRel {κ : Type} [BEq κ] [Hashable κ] (V : γ → δ → Prop) (m : Std.HashMap κ γ)
    (m' : Std.HashMap κ δ) : Prop :=
  ∀ (key : κ), ORel V m[key]? m'[key]?

section
variable {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]

theorem MapRel.empty (V : γ → δ → Prop) : MapRel V ({} : Std.HashMap κ γ) {} := by
  intro key
  simp [ORel]

theorem MapRel.insert {V : γ → δ → Prop} {m : Std.HashMap κ γ} {m' : Std.HashMap κ δ}
    (h : MapRel V m m') (k : κ) {v : γ} {v' : δ} (hv : V v v') :
    MapRel V (m.insert k v) (m'.insert k v') := by
  intro key
  simp only [Std.HashMap.getElem?_insert]
  split
  · exact hv
  · exact h key

end

def MapRelU {κ : Type} [BEq κ] [Hashable κ] (P : κ → Prop) (V : γ → δ → Prop) (m : Std.HashMap κ γ)
    (m' : Std.HashMap κ δ) : Prop :=
  ∀ (key : κ), P key → ORel V m[key]? m'[key]?

section
variable {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] {P : κ → Prop}

theorem MapRelU.empty (V : γ → δ → Prop) : MapRelU P V ({} : Std.HashMap κ γ) {} := by
  intro key _
  simp [ORel]

theorem MapRelU.insert {V : γ → δ → Prop} {m : Std.HashMap κ γ} {m' : Std.HashMap κ δ}
    (h : MapRelU P V m m') (k : κ) {v : γ} {v' : δ} (hv : V v v') :
    MapRelU P V (m.insert k v) (m'.insert k v') := by
  intro key hk
  simp only [Std.HashMap.getElem?_insert]
  split
  · exact hv
  · exact h key hk

theorem MapRelU.insert_out {V : γ → δ → Prop} {m : Std.HashMap κ γ} {m' : Std.HashMap κ δ}
    (h : MapRelU P V m m') {k k' : κ} (hk : ¬ P k) (hk' : ¬ P k') (v : γ) (v' : δ) :
    MapRelU P V (m.insert k v) (m'.insert k' v') := by
  intro key hkey
  have e1 : (k == key) = false := by
    simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk hkey
  have e2 : (k' == key) = false := by
    simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk' hkey
  simp only [Std.HashMap.getElem?_insert, e1, e2, Bool.false_eq_true, ite_false]
  exact h key hkey

end

theorem literalValue_two (f : Identifier) (x y : StmtExprMd) (r : List StmtExprMd) (ta : List HighTypeMd) :
    literalValue? (.Call none f (x :: y :: r) ta) = none := by
  rcases x with ⟨xv, _⟩
  cases xv <;> rfl

theorem ORel.orElse {V : γ → δ → Prop} {a b : Option γ} {a' b' : Option δ} (ha : ORel V a a')
    (hb : ORel V b b') : ORel V (a <|> b) (a' <|> b') := by
  cases a <;> cases a' <;> simp only [ORel] at ha <;> simp only [HOrElse.hOrElse, OrElse.orElse,
    Option.orElse] <;> first | exact hb | exact ha

theorem ORel.getD {V : γ → δ → Prop} {a : Option γ} {a' : Option δ} (h : ORel V a a') {d : γ} {d' : δ}
    (hd : V d d') : V (a.getD d) (a'.getD d') := by
  cases a <;> cases a' <;> simp only [ORel] at h <;> first | exact hd | exact h

theorem L2.map {R : α → β → Prop} {R' : γ → δ → Prop} {l : List α} {l' : List β} (h : L2 R l l')
    {f : α → γ} {g : β → δ} (hfg : ∀ a b, R a b → R' (f a) (g b)) : L2 R' (l.map f) (l'.map g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hfg _ _ hab) ih

theorem L2.flatMap_same {R : γ → δ → Prop} (l : List α) {f : α → List γ} {g : α → List δ}
    (h : ∀ a, L2 R (f a) (g a)) : L2 R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => simp only [List.flatMap_cons]; exact (h x).append ih

section
variable [Reserved] {E : StmtExprMd → StmtExprMd → Prop}

omit [Reserved] in
theorem foldl_nonAlias {F : β → TypeDefinition → β} (hF : ∀ acc a, F acc (.Alias a) = acc) (l : List TypeDefinition)
    (init : β) : l.foldl F init = (nonAliasTypes l).foldl F init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [nonAliasTypes, List.filter_cons, List.foldl_cons, hF] <;> exact ih _

omit [Reserved] in
theorem nonAlias_cons_alias (a : TypeAlias) (l : List TypeDefinition) :
    nonAliasTypes (.Alias a :: l) = nonAliasTypes l := by
  simp [nonAliasTypes]

omit [Reserved] in
theorem nonAlias_cons_other {x : TypeDefinition} (hx : ∀ a, x ≠ .Alias a) (l : List TypeDefinition) :
    nonAliasTypes (x :: l) = x :: nonAliasTypes l := by
  cases x <;> simp_all [nonAliasTypes]

omit [Reserved] in
theorem filterMap_nonAlias {f : TypeDefinition → Option α} (hf : ∀ a, f (.Alias a) = none) (l : List TypeDefinition) :
    (nonAliasTypes l).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : ∃ a, x = .Alias a
    · obtain ⟨a, rfl⟩ := hx
      rw [nonAlias_cons_alias, List.filterMap_cons, hf]
      exact ih
    · rw [nonAlias_cons_other (fun a h => hx ⟨a, h⟩), List.filterMap_cons, List.filterMap_cons, ih]

theorem L2.nonAlias {l l' : List TypeDefinition} (h : L2 (TypeRel E) l l') :
    L2 (TypeRel E) (nonAliasTypes l) (nonAliasTypes l') := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    cases hab with
    | alias a => rw [nonAlias_cons_alias, nonAlias_cons_alias]; exact ih
    | composite hc =>
      rw [nonAlias_cons_other (fun _ h => by cases h), nonAlias_cons_other (fun _ h => by cases h)]
      exact .cons (.composite hc) ih
    | constrained hc =>
      rw [nonAlias_cons_other (fun _ h => by cases h), nonAlias_cons_other (fun _ h => by cases h)]
      exact .cons (.constrained hc) ih
    | datatype hd =>
      rw [nonAlias_cons_other (fun _ h => by cases h), nonAlias_cons_other (fun _ h => by cases h)]
      exact .cons (.datatype hd) ih
    | opaque_ o =>
      rw [nonAlias_cons_other (fun _ h => by cases h), nonAlias_cons_other (fun _ h => by cases h)]
      exact .cons (.opaque_ o) ih

theorem DtRel.refl (hte : TyEq) (d : DatatypeDefinition) : DtRel d d := by
  refine ⟨rfl, ?_⟩
  generalize d.constructors = l
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons ⟨rfl, ParamR.list hte _⟩ ih

theorem L2.composites {l l' : List TypeDefinition} (h : L2 (TypeRel E) l l') :
    L2 (CompRel E)
      (l.filterMap fun t => match t with | .Composite ct => some ct | _ => none)
      (l'.filterMap fun t => match t with | .Composite ct => some ct | _ => none) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    cases hab with
    | composite hc => exact .cons hc ih
    | _ => exact ih

theorem collectFields_rel {defs : Std.HashMap String CompositeType} {defs' : Std.HashMap String CompositeType}
    (h : MapRel (CompRel E) defs defs') :
    ∀ d n, L2 (FieldRel E) (collectFields defs n d) (collectFields defs' n d) := by
  intro d
  induction d with
  | zero => intro n; simp only [collectFields]; exact .nil
  | succ d ih =>
    intro n
    simp only [collectFields]
    have hn := h n
    revert hn
    cases defs[n]? <;> cases defs'[n]? <;> simp only [ORel, false_implies, true_implies]
    · exact .nil
    · intro hc
      rw [← hc.extending]
      refine L2.append ?_ ?_
      · refine L2.flatMap_same _ (fun x => ?_)
        split
        · exact ih _
        · exact .nil
      · exact hc.fields.map (fun a b hab => ⟨by rw [hab.1], hab.2.1, hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2⟩)

theorem collectAncestors_eq {defs : Std.HashMap String CompositeType} {defs' : Std.HashMap String CompositeType}
    (h : MapRel (CompRel E) defs defs') :
    ∀ d n, collectAncestors defs' n d = collectAncestors defs n d := by
  intro d
  induction d with
  | zero => intro n; rfl
  | succ d ih =>
    intro n
    simp only [collectAncestors]
    have hn := h n
    revert hn
    cases defs[n]? <;> cases defs'[n]? <;> simp only [ORel, false_implies, true_implies]
    · intro hc
      rw [← hc.extending]
      congr 1
      congr 1
      funext x
      split
      · exact ih _
      · rfl


theorem L2.staticProcs {l l' : List Procedure} (h : L2 (ProcRel E) l l') :
    L2 (ProcRel E) (l.map fun pr => if pr.is_coroutine then liftCoroutineYields pr else pr)
      (l'.map fun pr => if pr.is_coroutine then liftCoroutineYields pr else pr) :=
  h.map (fun a b hab => by simp only [hab.coro, hab.coro', Bool.false_eq_true, ite_false]; exact hab)

omit [Reserved] in
theorem MapRel.bind_get {V : γ → δ → Prop} {m : Std.HashMap String (Std.HashMap String γ)}
    {m' : Std.HashMap String (Std.HashMap String δ)} (h : MapRel (MapRel V) m m') (t n : String) :
    ORel V (m[t]? >>= fun (x : Std.HashMap String γ) => x[n]?)
      (m'[t]? >>= fun (x : Std.HashMap String δ) => x[n]?) := by
  have := h t
  revert this
  cases m[t]? <;> cases m'[t]? <;> simp only [ORel, false_implies, Option.bind_eq_bind,
    Option.bind_none, Option.bind_some, imp_self]
  exact fun hx => hx n

set_option hygiene false in
macro "comp_tac" : tactic => `(tactic| (
  rw [foldl_nonAlias (l := p.types), foldl_nonAlias (l := q.types)]
  · refine h.types.foldl_rel (Inv := MapRel (CompRel E)) (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)
    cases hab with
    | composite hc => dsimp only; rw [hc.name]; exact hacc.insert _ hc
    | _ => exact hacc
  all_goals intro _ _; rfl))

omit [Reserved] in
theorem overloaded_contains (m : Std.HashMap String Nat) (n : String) :
    (m.fold (fun acc n k => if k > 1 then acc.insert n else acc) (∅ : Std.HashSet String)).contains n = true ↔
      ∃ k, m[n]? = some k ∧ k > 1 := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  have key : ∀ (l : List (String × Nat)) (acc : Std.HashSet String),
      (l.foldl (fun acc b => if b.2 > 1 then acc.insert b.1 else acc) acc).contains n = true ↔
        (acc.contains n = true ∨ ∃ k, (n, k) ∈ l ∧ k > 1) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      rcases b with ⟨b1, b2⟩
      dsimp only
      split
      · rename_i hb
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro ((h | h) | ⟨k, hk, hk1⟩)
          · subst h; exact .inr ⟨b2, .inl ⟨rfl, rfl⟩, hb⟩
          · exact .inl h
          · exact .inr ⟨k, .inr hk, hk1⟩
        · rintro (h | ⟨k, (⟨rfl, rfl⟩ | hk), hk1⟩)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr ⟨k, hk, hk1⟩
      · rename_i hb
        simp only [List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (h | ⟨k, hk, hk1⟩)
          · exact .inl h
          · exact .inr ⟨k, .inr hk, hk1⟩
        · rintro (h | ⟨k, (⟨rfl, rfl⟩ | hk), hk1⟩)
          · exact .inl h
          · exact absurd hk1 hb
          · exact .inr ⟨k, hk, hk1⟩
  rw [key]
  simp [Std.HashMap.mem_toList_iff_getElem?_eq_some]

theorem ProcRel.nameId {P P' : Procedure} (h : ProcRel E P P') : P'.name.uniqueId = P.name.uniqueId := by
  rcases h.name with h' | ⟨h', -⟩
  · rw [h']
  · exact h'.symm

theorem ProcRel.nameText {P P' : Procedure} (h : ProcRel E P P') :
    P'.name.text = P.name.text ∨ (Reserved.resProc P.name.text ∧ Reserved.resProc P'.name.text) := by
  rcases h.name with h' | ⟨-, ha, hb, -⟩
  · exact .inl (by rw [h'])
  · exact .inr ⟨ha, hb⟩

theorem MapRel.bind_getU {V : γ → δ → Prop} {m : Std.HashMap String (Std.HashMap String γ)}
    {m' : Std.HashMap String (Std.HashMap String δ)} (h : MapRel (MapRelU (fun k => ¬ Reserved.resProc k) V) m m')
    (t n : String) (hn : ¬ Reserved.resProc n) :
    ORel V (m[t]? >>= fun (x : Std.HashMap String γ) => x[n]?)
      (m'[t]? >>= fun (x : Std.HashMap String δ) => x[n]?) := by
  have := h t
  revert this
  cases m[t]? <;> cases m'[t]? <;> simp only [ORel, false_implies, Option.bind_eq_bind,
    Option.bind_none, Option.bind_some, imp_self]
  exact fun hx => hx n hn

omit [Reserved] in
theorem byId_some {l : List Procedure} {P : Procedure} (hP : P ∈ l) {id : Nat} (hid : P.name.uniqueId = some id)
    (acc : Std.HashMap Nat Procedure) :
    (l.foldl (fun acc pr => match pr.name.uniqueId with | some k => acc.insert k pr | none => acc) acc)[id]?.isSome := by
  have keep : ∀ (l : List Procedure) (acc : Std.HashMap Nat Procedure), acc[id]?.isSome →
      (l.foldl (fun acc pr => match pr.name.uniqueId with | some k => acc.insert k pr | none => acc) acc)[id]?.isSome := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x xs ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      cases x.name.uniqueId with
      | none => exact hacc
      | some k => simp only [Std.HashMap.getElem?_insert]; split <;> simp_all
  induction l generalizing acc with
  | nil => cases hP
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hP with rfl | hx
    · apply keep
      simp [hid]
    · exact ih hx _

omit [Reserved] in
theorem lift_name (pr : Procedure) :
    (if pr.is_coroutine then liftCoroutineYields pr else pr).name = pr.name := by
  split
  · unfold liftCoroutineYields; split <;> rfl
  · rfl

theorem consts_index {p q : LaurelProgram} (h : ConstsRel E p q) :
    ∀ (n : String), ¬ Reserved.resProc n → ORel (ConstRel E) ((buildIndex p).constants[n]?) ((buildIndex q).constants[n]?) := by
  obtain ⟨cs, extra, hq, hcs, hex⟩ := h
  intro n hn
  simp only [buildIndex, hq, List.foldl_append]
  have hx : ∀ (l : List Constant), (∀ x ∈ l, Reserved.resProc x.name.text) → ∀ (acc : Std.HashMap String Constant),
      (l.foldl (fun acc c => acc.insert c.name.text c) acc)[n]? = acc[n]? := by
    intro l hex acc
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (fun y hy => hex y (List.mem_cons_of_mem _ hy)), Std.HashMap.getElem?_insert]
      split
      · rename_i he; simp only [beq_iff_eq] at he; exact absurd (he ▸ hex x (List.mem_cons_self ..)) hn
      · rfl
  rw [hx extra hex]
  exact (hcs.foldl_rel (Inv := MapRelU (fun k => ¬ Reserved.resProc k) (ConstRel E))
    (fun acc acc' a b hacc hab => by rw [← hab.1]; exact hacc.insert _ hab.2) (MapRelU.empty _)) n hn

theorem aliasMap_rel {p q : List TypeDefinition} (h : L2 (TypeRel E) p q) : buildAliasMap q = buildAliasMap p := by
  unfold buildAliasMap
  exact (L2.foldl_congr h (fun acc a b hab => by cases hab <;> rfl) _).symm

omit [Reserved] in
theorem L2.zipIdx_rel {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') (n : Nat) :
    L2 (fun a b => R a.1 b.1 ∧ a.2 = b.2) (l.zipIdx n) (l'.zipIdx n) := by
  induction h generalizing n with
  | nil => exact .nil
  | cons hab _ ih => simp only [List.zipIdx_cons]; exact .cons ⟨hab, rfl⟩ (ih _)

def AliasU (ap aq : AliasMap) : Prop := ∀ t t', Reserved.tyR t t' → unaliasWith aq t' = unaliasWith ap t

theorem destrFold_rel {ap aq : AliasMap} (hu : AliasU ap aq) {d d' : DatatypeDefinition} (hdn : d.name = d'.name)
    {c c' : DatatypeConstructor} (hcn : c.name = c'.name) (hargs : L2 ParamR c.args c'.args)
    (ds : Std.HashMap String (String × Nat × HighType)) :
    c'.args.zipIdx.foldl (destrStep aq d' c') ds = c.args.zipIdx.foldl (destrStep ap d c) ds :=
  (L2.foldl_congr (hargs.zipIdx_rel 0) (fun acc a b hab => by
    simp only [destrStep, DatatypeDefinition.destructorName, hdn, hcn, hab.1.1, hab.2, hu _ _ hab.1.2]) ds).symm

theorem ctorFold_rel {ap aq : AliasMap} (hu : AliasU ap aq) {d d' : DatatypeDefinition} (hd : DtRel d d')
    (acc : DtTables) : d'.constructors.foldl (ctorStep aq d') acc = d.constructors.foldl (ctorStep ap d) acc :=
  (L2.foldl_congr hd.2 (fun acc c c' hcc => by
    have hnm : c.args.map (·.name.text) = c'.args.map (·.name.text) :=
      L2.map_eq hcc.2 (fun x y hxy => by rw [hxy.1])
    simp only [ctorStep, DatatypeDefinition.testerName, hd.1, hcc.1, hnm, destrFold_rel hu hd.1 hcc.1 hcc.2]) acc).symm

theorem datatypeTables_rel {ap aq : AliasMap} (hu : AliasU ap aq) {l l' : List TypeDefinition}
    (h : L2 (TypeRel E) (nonAliasTypes l) (nonAliasTypes l')) : datatypeTables aq l' = datatypeTables ap l := by
  unfold datatypeTables
  rw [foldl_nonAlias (F := typeStep ap) (fun _ _ => rfl) l, foldl_nonAlias (F := typeStep aq) (fun _ _ => rfl) l']
  refine (L2.foldl_congr h (fun acc a b hab => ?_) _).symm
  cases hab with
  | datatype hd => exact (ctorFold_rel hu hd acc).symm
  | _ => rfl

theorem aliasOK_of (hte : TyEq) {p q : LaurelProgram} (h : L2 (TypeRel E) p.types q.types) : AliasOK p q := by
  intro t t' ht
  rw [(hte t t').mp ht, aliasMap_rel h]

omit [Reserved] in
theorem heapFields_index {p q : LaurelProgram} (h : HeapKeys q = HeapKeys p) :
    (buildIndex q).heapFields = (buildIndex p).heapFields := by
  have key : ∀ r : LaurelProgram, (buildIndex r).heapFields =
      (HeapKeys r).foldl (fun acc k => acc.insert k.1 (k.2.1, k.2.2)) {} := by
    intro r
    simp only [buildIndex, HeapKeys, List.foldl_map]
  rw [key q, key p, h]

omit [Reserved] in
theorem foldl_insert_mem (l : List (String × String × HighType))
    (acc : Std.HashMap String (String × HighType)) (n : String) (v : String × HighType)
    (h : (l.foldl (fun acc k => acc.insert k.1 (k.2.1, k.2.2)) acc)[n]? = some v) :
    (n, v.1, v.2) ∈ l ∨ acc[n]? = some v := by
  induction l generalizing acc with
  | nil => exact .inr h
  | cons k l ih =>
    rcases ih _ h with hm | hm
    · exact .inl (List.mem_cons_of_mem _ hm)
    · rw [Std.HashMap.getElem?_insert] at hm
      split at hm
      · rename_i he
        simp only [beq_iff_eq] at he
        subst he
        cases hm
        exact .inl (List.mem_cons_self ..)
      · exact .inr hm

theorem heapTy_index {p : LaurelProgram} (h : ∀ k ∈ HeapKeys p, Reserved.tyR k.2.2 k.2.2) :
    ∀ (n loc : String) (t : HighType), (buildIndex p).heapFields[n]? = some (loc, t) → Reserved.tyR t t := by
  intro n loc t hn
  have key : (buildIndex p).heapFields =
      (HeapKeys p).foldl (fun acc k => acc.insert k.1 (k.2.1, k.2.2)) {} := by
    simp only [buildIndex, HeapKeys, List.foldl_map]
  rw [key] at hn
  rcases foldl_insert_mem _ _ _ _ hn with hm | hm
  · exact h _ hm
  · simp at hm

theorem constraintChain_rel {ap aq : AliasMap} (hu : AliasU ap aq) {m m' : Std.HashMap String ConstrainedType}
    (h : MapRel (ConsRel E) m m') :
    ∀ fuel c c', ConsRel E c c' → L2 (ConsRel E) (constraintChain ap m fuel c) (constraintChain aq m' fuel c') := by
  intro fuel
  induction fuel with
  | zero => intro c c' hc; exact .cons hc .nil
  | succ k ih =>
    intro c c' hc
    simp only [constraintChain]
    rw [hu _ _ hc.base]
    split
    · rename_i n _
      have := h n.text
      revert this
      cases m[n.text]? <;> cases m'[n.text]? <;> simp only [ORel, false_implies, true_implies]
      · exact .cons hc .nil
      · exact fun hb => .cons hc (ih _ _ hb)
    · exact .cons hc .nil

omit [Reserved] in
theorem L2.getLast?_getD {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') {d : α} {d' : β}
    (hd : R d d') : R (l.getLast?.getD d) (l'.getLast?.getD d') := by
  induction h with
  | nil => exact hd
  | cons hab ht ih =>
    cases ht with
    | nil => exact hab
    | cons => simpa only [List.getLast?_cons_cons] using ih

theorem exceptionBases_index {p q : LaurelProgram} (h : ProgRel0 E p q) :
    (buildIndex q).exceptionBases = (buildIndex p).exceptionBases := by
  have hm : MapRel (ConsRel E)
      (p.types.foldl (init := {}) fun acc t => match t with | .Constrained c => acc.insert c.name.text c | _ => acc)
      (q.types.foldl (init := {}) fun acc t => match t with | .Constrained c => acc.insert c.name.text c | _ => acc) := by
    rw [foldl_nonAlias (l := p.types), foldl_nonAlias (l := q.types)]
    · refine h.types.foldl_rel (Inv := MapRel (ConsRel E)) (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)
      cases hab with
      | constrained hc => dsimp only; rw [hc.name]; exact hacc.insert _ hc
      | _ => exact hacc
    all_goals intro _ _; rfl
  have hl := h.types.length_eq
  simp only [buildIndex]
  rw [foldl_nonAlias (l := p.types), foldl_nonAlias (l := q.types)]
  · refine (L2.foldl_congr h.types (fun acc a b hab => ?_) _).symm
    cases hab with
    | constrained hc =>
      dsimp only
      rw [hc.name, hl]
      exact congrArg _ (h.unalias _ _ (L2.getLast?_getD (constraintChain_rel h.unalias hm _ _ _ hc) hc).base).symm
    | _ => rfl
  all_goals intro _ _; rfl

/-- If two programs are related by `ProgRel0 E` (their functions and procedures, types, constants and
heap fields correspond, with no extra procedures), then their program indices `buildIndex p` and
`buildIndex q` are related by `IxRel0 E`: every lookup of a name that is not reserved gives related
results in the two indices. -/
theorem ProgRel0.index {p q : LaurelProgram} (h : ProgRel0 E p q) : IxRel0 E (buildIndex p) (buildIndex q) := by
  have hsp := h.procs.staticProcs
  have hcl : L2 (CompRel E) (p.types.filterMap fun t => match t with | .Composite ct => some ct | _ => none)
      (q.types.filterMap fun t => match t with | .Composite ct => some ct | _ => none) := by
    have := h.types.composites
    rw [filterMap_nonAlias, filterMap_nonAlias] at this
    · exact this
    all_goals intro _; rfl
  have hlen : compositeCount p.types = compositeCount q.types := hcl.length_eq
  have hbyId : MapRel (ProcRel E) (buildIndex p).procsById (buildIndex q).procsById := by
    simp only [buildIndex]
    refine hsp.foldl_rel (Inv := MapRel (ProcRel E)) (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)
    rw [hab.nameId]
    cases a.name.uniqueId with
    | none => exact hacc
    | some k => exact hacc.insert _ hab
  have hcount : ∀ key, ¬ Reserved.resProc key →
      ((p.staticFunctions ++ p.staticProcedures).foldl (init := ({} : Std.HashMap String Nat)) fun acc pr =>
        acc.insert pr.name.text (acc.getD pr.name.text 0 + 1))[key]? =
      ((q.staticFunctions ++ q.staticProcedures).foldl (init := ({} : Std.HashMap String Nat)) fun acc pr =>
        acc.insert pr.name.text (acc.getD pr.name.text 0 + 1))[key]? := by
    refine h.procs.foldl_rel (Inv := fun m m' => ∀ key, ¬ Reserved.resProc key → m[key]? = m'[key]?)
      (fun acc acc' a b hacc hab => ?_) (fun _ _ => rfl)
    intro key hk
    rcases hab.nameText with he | ⟨ha, hb⟩
    · rw [he]
      simp only [Std.HashMap.getElem?_insert]
      split
      · rename_i hkey
        simp only [beq_iff_eq] at hkey
        subst hkey
        simp only [Std.HashMap.getD_eq_getD_getElem?, hacc _ hk]
      · exact hacc key hk
    · have e1 : (a.name.text == key) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk ha
      have e2 : (b.name.text == key) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk hb
      simp only [Std.HashMap.getElem?_insert, e1, e2, Bool.false_eq_true, ite_false]
      exact hacc key hk
  constructor
  · intro c hc
    replace hc := not_resProc_of_call hc
    show ORel _ ((c.uniqueId.bind (buildIndex p).procsById.get?) <|> (buildIndex p).procs[c.text]?)
      ((c.uniqueId.bind (buildIndex q).procsById.get?) <|> (buildIndex q).procs[c.text]?)
    refine ORel.orElse ?_ ?_
    · cases c.uniqueId with
      | none => trivial
      | some id =>
        simp only [Option.bind_some, Std.HashMap.get?_eq_getElem?]
        exact hbyId id
    · simp only [buildIndex]
      refine (hsp.foldl_rel (Inv := MapRelU (fun k => ¬ Reserved.resProc k) (ProcRel E))
        (fun acc acc' a b hacc hab => ?_) (MapRelU.empty _)) c.text hc
      rcases hab.nameText with he | ⟨ha, hb⟩
      · rw [he]; exact hacc.insert _ hab
      · exact hacc.insert_out (fun h => h ha) (fun h => h hb) _ _
  · intro n hn
    simp only [buildIndex]
    rw [Bool.eq_iff_iff, overloaded_contains, overloaded_contains, hcount n hn]
  · intro f f' hr
    obtain ⟨hid, id, P0, hfid, hP0, hP0id⟩ := h.renOK f f' hr
    have hs : (buildIndex p).procsById[id]?.isSome := by
      simp only [buildIndex]
      exact byId_some (l := (p.staticFunctions ++ p.staticProcedures).map fun pr =>
          if pr.is_coroutine then liftCoroutineYields pr else pr)
        (P := if P0.is_coroutine then liftCoroutineYields P0 else P0)
        (List.mem_map.mpr ⟨P0, List.mem_append_right _ hP0, rfl⟩) (by rw [lift_name]; exact hP0id) _
    have hb := hbyId id
    revert hb hs
    cases e1 : (buildIndex p).procsById[id]? <;> cases e2 : (buildIndex q).procsById[id]? <;>
      simp only [ORel, false_implies, Option.isSome_none, Bool.false_eq_true, implies_true, true_implies]
    rename_i P P'
    intro _ hPP
    refine ⟨P, P', ?_, ?_, hPP⟩
    · simp only [hfid, Option.bind_some, Std.HashMap.get?_eq_getElem?, e1]
    · simp only [hid, hfid, Option.bind_some, Std.HashMap.get?_eq_getElem?, e2]
  · intro hrm t n hn
    simp only [buildIndex]
    refine MapRel.bind_getU (hcl.foldl_rel (Inv := MapRel (MapRelU (fun k => ¬ Reserved.resProc k) (ProcRel E)))
      (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)) t n hn
    rw [← hab.name]
    refine hacc.insert _ ?_
    exact (hab.procs hrm).foldl_rel (Inv := MapRelU (fun k => ¬ Reserved.resProc k) (ProcRel E)) (fun m m' x y hm hxy => by
      rw [hxy.2.1]; exact hm.insert _ hxy.1) (MapRelU.empty _)
  · intro hrm id
    simp only [buildIndex]
    refine (hcl.foldl_rel (Inv := MapRel (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs))
      (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)) id
    exact (hab.procs hrm).foldl_rel (Inv := MapRel (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs))
      (fun m m' x y hm hxy => by
        rw [hxy.1.nameId]
        cases x.name.uniqueId with
        | none => exact hm
        | some k => exact hm.insert _ hxy) hacc
  · intro hrm
    simp only [buildIndex]
    refine (L2.foldl_congr hcl (fun acc a b hab => ?_) _).symm
    rw [hab.name]
    refine L2.foldl_congr (hab.procs hrm) ?_ _
    intro m x y hxy
    rw [hxy.1.nameId]
  · intro hrm t
    simp only [buildIndex]
    refine ORel.getD ((hcl.foldl_rel (Inv := MapRel (L2 (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)))
      (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)) t) .nil
    rw [← hab.name]
    exact hacc.insert _ (hab.procs hrm)
  · simp only [buildIndex]
    rw [← hlen]
    refine (L2.foldl_congr hcl (fun acc a b hab => ?_) _).symm
    rw [hab.name]
    congr 1
    refine (collectAncestors_eq (E := E) ?_ _ _).symm
    comp_tac
  · intro nm
    simp only [buildIndex]
    rw [← hlen]
    refine ORel.getD ((hcl.foldl_rel (Inv := MapRel (L2 (FieldRel E)))
      (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)) nm) .nil
    rw [← hab.name]
    refine hacc.insert _ (collectFields_rel (E := E) ?_ _ _)
    comp_tac
  · intro nm hn
    simp only [buildIndex]
    refine (hsp.foldl_rel (Inv := fun (m m' : Std.HashMap String (List Procedure)) =>
      ∀ key, ¬ Reserved.resProc key → L2 (ProcRel E) (m[key]?.getD []) (m'[key]?.getD []))
      (fun acc acc' a b hacc hab => ?_) (fun _ _ => by simp only [Std.HashMap.not_mem_empty, not_false_eq_true, getElem?_neg, Option.getD_none]; exact .nil)) nm hn
    intro key hk
    rcases hab.nameText with he | ⟨ha, hb⟩
    · rw [he]
      simp only [Std.HashMap.getElem?_insert, Std.HashMap.getD_eq_getD_getElem?]
      split
      · rename_i hkey
        simp only [beq_iff_eq] at hkey
        subst hkey
        exact (hacc _ hk).append (.cons hab .nil)
      · exact hacc key hk
    · have e1 : (a.name.text == key) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk ha
      have e2 : (b.name.text == key) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hk hb
      simp only [Std.HashMap.getElem?_insert, e1, e2, Bool.false_eq_true, ite_false]
      exact hacc key hk
  all_goals
    first
    | exact consts_index h.consts
    | exact heapFields_index h.heapFields
    | exact heapTy_index h.heapTy
    | exact exceptionBases_index h
    | skip
  all_goals
    first
    | exact h.unalias
    | skip
  all_goals
    simp only [buildIndex]
    first
    | done
    | rfl
    | exact congrArg Prod.fst (datatypeTables_rel h.unalias h.types)
    | exact congrArg (Prod.fst ∘ Prod.snd) (datatypeTables_rel h.unalias h.types)
    | exact congrArg (Prod.snd ∘ Prod.snd) (datatypeTables_rel h.unalias h.types)
    | (rw [foldl_nonAlias (l := p.types), foldl_nonAlias (l := q.types)]
       · refine (L2.foldl_congr h.types (fun acc a b hab => ?_) _).symm
         cases hab with
         | constrained hc => dsimp only; rw [hc.name, hc.literal]
         | _ => rfl
       all_goals intro _ _; rfl)

theorem foldl_insert_reserved {β : Type} (l : List Procedure) (acc : Std.HashMap String β)
    (val : Std.HashMap String β → Procedure → β) (hl : ∀ x ∈ l, Reserved.resProc x.name.text)
    {k : String} (hk : ¬ Reserved.resProc k) :
    (l.foldl (fun acc x => acc.insert x.name.text (val acc x)) acc)[k]? = acc[k]? := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)), Std.HashMap.getElem?_insert]
    split
    · rename_i he; simp only [beq_iff_eq] at he; exact absurd (he ▸ hl x (List.mem_cons_self ..)) hk
    · rfl

theorem IxRel0.extend {ix ix1 ix2 : ProgramIndex} (h : IxRel0 E ix ix1)
    (hc : ∀ c, ¬ Reserved.resCall c → lookupCallee ix2 c = lookupCallee ix1 c)
    (hbi : ix2.procsById = ix1.procsById)
    (ho : ∀ n, ¬ Reserved.resProc n → ix2.overloaded.contains n = ix1.overloaded.contains n)
    (hn : ∀ n, ¬ Reserved.resProc n → ix2.procsNamed[n]? = ix1.procsNamed[n]?)
    (hm : ix2.methods = ix1.methods) (hmb : ix2.methodsById = ix1.methodsById)
    (hmo : ix2.methodOwner = ix1.methodOwner) (hml : ix2.methodLists = ix1.methodLists) (ha : ix2.ancestors = ix1.ancestors)
    (hf : ix2.compositeFields = ix1.compositeFields) (hct : ix2.ctors = ix1.ctors) (ht : ix2.testers = ix1.testers)
    (hd : ix2.destructors = ix1.destructors) (hw : ix2.witnesses = ix1.witnesses)
    (hnw : ix2.noWitness = ix1.noWitness) (heb : ix2.exceptionBases = ix1.exceptionBases) (hal : ix2.aliasMap = ix1.aliasMap)
    (hcs : ix2.constants = ix1.constants) (hhf : ix2.heapFields = ix1.heapFields)
    (hx : Reserved.ixX E ix ix2) : IxRel E ix ix2 where
  heapFields := by rw [hhf]; exact h.heapFields
  heapTy := h.heapTy
  callee c hr := by rw [hc c hr]; exact h.callee c hr
  renCallee f f' hr := by rw [hbi]; exact h.renCallee f f' hr
  overloaded n hr := by rw [ho n hr]; exact h.overloaded n hr
  methods hr t n hn := by rw [hm]; exact h.methods hr t n hn
  methodsById hr id := by rw [hmb]; exact h.methodsById hr id
  methodOwner hr := by rw [hmo]; exact h.methodOwner hr
  methodLists hr t := by rw [hml]; exact h.methodLists hr t
  ancestors := by rw [ha]; exact h.ancestors
  fields n := by rw [hf]; exact h.fields n
  procsNamed n hr := by rw [hn n hr]; exact h.procsNamed n hr
  ctors := by rw [hct]; exact h.ctors
  testers := by rw [ht]; exact h.testers
  destructors := by rw [hd]; exact h.destructors
  witnesses := by rw [hw]; exact h.witnesses
  noWitness := by rw [hnw]; exact h.noWitness
  exceptionBases := by rw [heb]; exact h.exceptionBases
  unalias t t' ht := by unfold ProgramIndex.unalias; rw [hal]; exact h.unalias t t' ht
  consts n hn := by rw [hcs]; exact h.consts n hn
  extra := hx

omit [Reserved] in
theorem foldl_fix {l : List α} {F : β → α → β} (acc : β) (h : ∀ acc, ∀ x ∈ l, F acc x = acc) :
    l.foldl F acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, h acc x (List.mem_cons_self ..)]
    exact ih _ (fun a y hy => h a y (List.mem_cons_of_mem _ hy))

/-- If two programs are related by `ProgRel E`, where the target may have extra procedures with
reserved names, then their program indices `buildIndex p` and `buildIndex q` are related by
`IxRel E`: `IxRel0 E`, plus the pass's own index relation `Reserved.ixX`. -/
theorem ProgRel.index {p q : LaurelProgram} (h : ProgRel E p q) : IxRel E (buildIndex p) (buildIndex q) := by
  obtain ⟨ps, extra, hq, hps, hex⟩ := h.procs
  have h0 : IxRel0 E (buildIndex p) (buildIndex { q with staticProcedures := ps }) :=
    ProgRel0.index ⟨h.funs.append hps, h.types, h.renOK, h.consts, h.unalias, h.heapFields, h.heapTy⟩
  have hexl : ∀ x ∈ extra.map (fun pr => if pr.is_coroutine then liftCoroutineYields pr else pr),
      Reserved.resProc x.name.text ∧ x.name.uniqueId = none := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [lift_name]; exact hex y hy
  refine h0.extend (fun c hc => ?_) ?_ (fun n hn => ?_) (fun n hn => ?_) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h.ixX
  · simp only [lookupCallee, buildIndex, hq, List.map_append, List.foldl_append, ← List.append_assoc]
    rw [foldl_fix _ (fun acc x hx => by simp only [(hexl x hx).2]),
      foldl_insert_reserved _ _ (fun _ x => x) (fun x hx => (hexl x hx).1) (not_resProc_of_call hc)]
  · simp only [buildIndex, hq, List.map_append, List.foldl_append, ← List.append_assoc]
    rw [foldl_fix _ (fun acc x hx => by simp only [(hexl x hx).2])]
  · simp only [buildIndex, hq, List.foldl_append, ← List.append_assoc]
    have hi := foldl_insert_reserved extra (List.foldl (fun acc pr => acc.insert pr.name.text
      (acc.getD pr.name.text 0 + 1)) (List.foldl (fun acc pr => acc.insert pr.name.text
      (acc.getD pr.name.text 0 + 1)) ∅ q.staticFunctions) ps) (fun acc pr => acc.getD pr.name.text 0 + 1)
      (fun x hx => (hex x hx).1) hn
    rw [Bool.eq_iff_iff, overloaded_contains, overloaded_contains, hi]
  · simp only [buildIndex, hq, List.map_append, List.foldl_append, ← List.append_assoc]
    exact foldl_insert_reserved _ _ (fun acc pr => acc.getD pr.name.text [] ++ [pr])
      (fun x hx => (hexl x hx).1) hn

end

end Strata.Laurel.PassSemantics